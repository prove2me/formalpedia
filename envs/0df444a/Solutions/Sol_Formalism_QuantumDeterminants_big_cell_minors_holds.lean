-- Prove2me | solution 1 for Formalism.QuantumDeterminants.big_cell_minors_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T11:33:21.328307+00:00
-- url     : https://prove2.me/submissions/74949286-e5ac-4245-92a9-94eedc5b8afb

import Definitions.Def_Formalism_FormalDegreeBessel_StatementBF
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GroupFactorizationHolds
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_BFCell
import Theorems.Thm_Formalism_QuantumDeterminants_BruhatBigCell_dmin_diag
import Theorems.Thm_Formalism_QuantumDeterminants_big_cell_coordinate_holds

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
noncomputable section
open Formalism Formalism.QuantumDeterminants
open GBasic BruhatBigCell
namespace Formalism.QuantumDeterminants
theorem _root_.solution : BigCellMinors := by
  intro k r z z' c μ hz hz'
  have hZ := big_cell_coordinate_holds k r z z' c μ hz hz'
  set d : Fin (r + 1) → ℂ := fun a => if h : a.val < r then c ⟨a.val, h⟩ else
    herm (Hpk k r) (bigCell k r c μ *ᵥ z') z with hd
  have hD := dmin_diag z z' (bigCell k r c μ) d hZ
  have hlo : ∀ (x : Fin (r + 1)) (hx : x.val < r), d x = c ⟨x.val, hx⟩ := by
    intro x hx; simp only [hd]; rw [dif_pos hx]
  have part1 : ∀ l : Fin (r + 1), Dmin k r z z' (bigCell k r c μ) ⟨l.val, by omega⟩ =
      ∏ a : Fin r with a.val < l.val, c a := by
    intro l
    rw [hD]
    have hl : l.val ≤ r := by omega
    have hs : (Finset.univ.filter fun a : Fin r => a.val < l.val) =
        Finset.univ.map (Fin.castLEEmb hl) := by
      ext a
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map, Fin.castLEEmb]
      constructor
      · intro h; exact ⟨⟨a.val, h⟩, Fin.ext rfl⟩
      · rintro ⟨i, hi⟩; rw [← hi]; exact i.isLt
    rw [hs, Finset.prod_map]
    apply Finset.prod_congr rfl
    intro i _
    rw [hlo _ (by simp only [Fin.val_castLE]; omega)]
    rfl
  refine ⟨part1, ?_, ?_⟩
  · intro hc a
    unfold cmin
    have e1 := part1 ⟨a.val + 1, by omega⟩
    have e2 := part1 ⟨a.val, by omega⟩
    simp only at e1 e2
    rw [e1, e2]
    have hs : (Finset.univ.filter fun b : Fin r => b.val < a.val + 1) =
        insert a (Finset.univ.filter fun b : Fin r => b.val < a.val) := by
      ext b
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Fin.ext_iff]
      omega
    have hP : (∏ b : Fin r with b.val < a.val, c b) ≠ 0 :=
      Finset.prod_ne_zero_iff.2 (fun b _ => hc b)
    rw [hs, Finset.prod_insert (by simp), mul_div_assoc, div_self hP, mul_one]
  · intro hc
    unfold zeta
    rw [hD, hD]
    show (∏ i : Fin (r + 1), d (Fin.castLE _ i)) / (∏ i : Fin r, d (Fin.castLE _ i)) = _
    rw [Fin.prod_univ_castSucc]
    have e1 : ∀ i : Fin r, d (Fin.castLE (le_refl (r + 1)) (Fin.castSucc i)) = c i := by
      intro i; rw [hlo _ (by simp)]; rfl
    have e2 : ∀ i : Fin r, d (Fin.castLE (Nat.le_succ r) i) = c i := by
      intro i; rw [hlo _ (by simp)]; rfl
    have e3 : d (Fin.castLE (le_refl (r + 1)) (Fin.last r)) =
        herm (Hpk k r) (bigCell k r c μ *ᵥ z') z := by
      simp only [hd]; rw [dif_neg (by simp)]
    simp only [e1, e2, e3]
    have hP : (∏ i : Fin r, c i) ≠ 0 := Finset.prod_ne_zero_iff.2 (fun b _ => hc b)
    rw [mul_comm, mul_div_assoc, div_self hP, mul_one]
end Formalism.QuantumDeterminants
