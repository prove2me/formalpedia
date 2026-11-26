-- Prove2me | solution 1 for CSeparatedNPComplete.SquareReduction.exists_ec_partition_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:57:28.650818+00:00
-- url     : https://prove2.me/submissions/4ddda4e6-6186-425d-93a4-484fed2fcd93

module
public import Definitions.Def_CSeparatedNPComplete_SquarePartition
public import Definitions.Def_CSeparatedNPComplete_SquareReduction
public import Theorems.Thm_CSeparatedNPComplete_SquareReduction_base_ge_two
public import Theorems.Thm_CSeparatedNPComplete_SquareReduction_forces_pairs
public import Theorems.Thm_CSeparatedNPComplete_SquareReduction_paired_balance_identity
public import Theorems.Thm_CSeparatedNPComplete_SquareReduction_paired_card

set_option autoImplicit true
@[expose] public section
public section
open CSeparatedNPComplete CSeparatedNPComplete.SquareReduction
namespace CSeparatedNPComplete.SquareReduction
theorem _root_.solution {n : ℕ} (a : Fin n → ℕ) :
    (∃ x : Vec (n + n), is_ec_partition x (values a)) ↔ HasPartition a := by
  have hK := base_ge_two a
  have hfactor : 0 < 4 * (base a : ℝ) ^ (2 * n) := by
    have : 0 < (base a : ℝ) := by exact_mod_cast (show 0 < base a by omega)
    positivity
  constructor
  · rintro ⟨x, hxbin, _, hxbal⟩
    let p : Vec n := fun i => x (Fin.castAdd n i)
    let q : Vec n := fun i => x (Fin.natAdd n i)
    have hx : Fin.append p q = x := Fin.append_castAdd_natAdd
    have hp : is_binary p := fun i => hxbin _
    have hq : is_binary q := fun i => hxbin _
    have hpq := forces_pairs a p q hp hq (by rwa [hx])
    have hqeq : q = 1 - p := by
      funext i
      have := hpq i
      simp only [Pi.sub_apply, Pi.one_apply]
      linarith
    refine ⟨p, hp, ?_⟩
    have hid := paired_balance_identity a p
    rw [← hqeq, hx, hxbal, sub_self] at hid
    nlinarith
  · rintro ⟨p, hp, hbal⟩
    refine ⟨Fin.append p (1 - p), ?_, paired_card p, ?_⟩
    · intro i
      refine Fin.addCases ?_ ?_ i
      · intro j
        simpa only [Fin.append_left] using hp j
      · intro j
        simp only [Fin.append_right, Pi.sub_apply, Pi.one_apply]
        rcases hp j with h | h <;> simp [h]
    · have hid := paired_balance_identity a p
      rw [hbal, sub_self, mul_zero] at hid
      linarith
end CSeparatedNPComplete.SquareReduction
