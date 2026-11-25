-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.coeff_subst_bil
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T01:31:20.51109+00:00
-- url     : https://prove2.me/submissions/cb508e1a-9e35-43cd-81ce-3e0a2a292fd0

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieCartFB
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTiePHStab
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_Van_mul_left
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_van_prod
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_coeff_mul_van_van
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_exchangeTwo_self_eq_one
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_elementary_pair_apply_second
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_elementary_pair_eq_zero_of_ne
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_elementary_pair_support
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_coeff_mul_van_two
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_elementary_pair_injective
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_prod
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_Van_subst


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds
open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ MvPowerSeries
variable {C : Type} [Field C]
variable {τ κ : Type} [Fintype κ]
namespace Formalism.L2.FormalSeriesBounds
theorem _root_.solution {T1 T2 : Set τ} {a : Fin 2 × κ → MvPowerSeries τ C}
    (ha0 : ∀ s, constantCoeff (a s) = 0) (hax : ∀ i, Van T1 (a (0, i))) (haz : ∀ j, Van T2 (a (1, j)))
    {P Q : τ} (hPQ : P ≠ Q) (hQ : Q ∉ T1) (hP : P ∉ T2) {h : MvPowerSeries (Fin 2 × κ) C}
    (hh : ∀ (g : Fin 2) (e : Fin 2 × κ →₀ ℕ), (∀ s ∈ e.support, s.1 ≠ g) → coeff e h = 0) :
    coeff (E2 P Q) (MvPowerSeries.subst a h) =
      ∑ i, ∑ j, coeff (E2 ((0 : Fin 2), i) ((1 : Fin 2), j)) h *
        (coeff (Finsupp.single P 1) (a (0, i)) * coeff (Finsupp.single Q 1) (a (1, j))) := by
  have hne : ∀ x y : κ, ((0 : Fin 2), x) ≠ ((1 : Fin 2), y) := fun x y e => by
    have h01 : (0 : Fin 2) = 1 := congrArg Prod.fst e
    exact absurd h01 (by decide)
  have he1 : ∀ s ∈ T1, E2 P Q s ≠ 0 → s = P := fun s hs h0 => by
    rcases elementary_pair_support h0 with e | e
    · exact e
    · exact absurd (e ▸ hs) hQ
  have he2 : ∀ s ∈ T2, E2 P Q s ≠ 0 → s = Q := fun s hs h0 => by
    rcases elementary_pair_support h0 with e | e
    · exact absurd (e ▸ hs) hP
    · exact e
  rw [coeff_subst (hasSubst_of_constantCoeff_zero ha0)]
  have hprod : ∀ (i j : κ) (d' : Fin 2 × κ →₀ ℕ),
      ((E2 ((0 : Fin 2), i) ((1 : Fin 2), j) + d').prod fun s m => a s ^ m) =
        a (0, i) * a (1, j) * d'.prod fun s m => a s ^ m := by
    intro i j d'
    unfold E2
    rw [Finsupp.prod_add_index' (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _),
      Finsupp.prod_add_index' (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _),
      Finsupp.prod_single_index (h := fun s m => a s ^ m) (pow_zero _),
      Finsupp.prod_single_index (h := fun s m => a s ^ m) (pow_zero _), pow_one, pow_one]
  have hsupp : (Function.support fun d : Fin 2 × κ →₀ ℕ =>
      coeff d h • coeff (E2 P Q) (d.prod fun s m => a s ^ m)) ⊆
      ↑((Finset.univ : Finset (κ × κ)).image fun ij => E2 ((0 : Fin 2), ij.1) ((1 : Fin 2), ij.2)) := by
    intro d hd
    by_contra hnot
    apply hd
    show coeff d h • coeff (E2 P Q) (d.prod fun s m => a s ^ m) = 0
    by_cases hx : ∀ s ∈ d.support, s.1 ≠ 0
    · rw [hh 0 d hx, zero_smul]
    by_cases hz : ∀ s ∈ d.support, s.1 ≠ 1
    · rw [hh 1 d hz, zero_smul]
    push Not at hx hz
    obtain ⟨⟨g, i⟩, hs, hg⟩ := hx
    obtain ⟨⟨g', j⟩, hs', hg'⟩ := hz
    have hg0 : g = 0 := hg
    have hg1 : g' = 1 := hg'
    subst hg0
    subst hg1
    have hle : E2 ((0 : Fin 2), i) ((1 : Fin 2), j) ≤ d := by
      intro x
      by_cases h1 : x = ((0 : Fin 2), i)
      · rw [h1, exchangeTwo_self_eq_one (hne i j)]
        exact Nat.one_le_iff_ne_zero.2 (Finsupp.mem_support_iff.1 hs)
      · by_cases h2 : x = ((1 : Fin 2), j)
        · rw [h2, elementary_pair_apply_second (hne i j)]
          exact Nat.one_le_iff_ne_zero.2 (Finsupp.mem_support_iff.1 hs')
        · rw [elementary_pair_eq_zero_of_ne h1 h2]
          exact Nat.zero_le _
    have hd' : d = E2 ((0 : Fin 2), i) ((1 : Fin 2), j) + (d - E2 ((0 : Fin 2), i) ((1 : Fin 2), j)) :=
      (add_tsub_cancel_of_le hle).symm
    set d' := d - E2 ((0 : Fin 2), i) ((1 : Fin 2), j) with hd'def
    have hd'0 : d' ≠ 0 := by
      intro h0
      apply hnot
      rw [Finset.coe_image, Set.mem_image]
      exact ⟨(i, j), by simp, by rw [hd', h0, add_zero]⟩
    obtain ⟨⟨g'', t⟩, hs''⟩ := Finsupp.support_nonempty_iff.2 hd'0
    rw [hd', hprod]
    have hall : ∀ x : Fin 2, x = 0 ∨ x = 1 := by decide
    have hcase : g'' = 0 ∨ g'' = 1 := hall g''
    rcases hcase with rfl | rfl
    · rw [mul_assoc, coeff_mul_van_van (hax i) ((van_prod hs'' (hax t)).mul_left _) (E2 P Q) P he1
        (le_of_eq (exchangeTwo_self_eq_one hPQ)), smul_zero]
    · rw [mul_comm (a (0, i)), mul_assoc, coeff_mul_van_van (haz j) ((van_prod hs'' (haz t)).mul_left _) (E2 P Q) Q he2
        (le_of_eq (elementary_pair_apply_second hPQ)), smul_zero]
  rw [finsum_eq_sum_of_support_subset _ hsupp, Finset.sum_image, Fintype.sum_prod_type]
  · apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    have := hprod i j 0
    rw [add_zero, Finsupp.prod_zero_index, mul_one] at this
    rw [this, coeff_mul_van_two (hax i) (haz j) hPQ hQ hP, smul_eq_mul]
  · intro x _ y _ hxy
    obtain ⟨h1, h2⟩ := elementary_pair_injective hxy
    exact Prod.ext h1 h2
end Formalism.L2.FormalSeriesBounds
