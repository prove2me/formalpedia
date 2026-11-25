-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.reduce_to_boxes
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T16:50:53.191092+00:00
-- url     : https://prove2.me/submissions/a6759c0b-7e26-4b47-8fb4-f9c0426b388d

import Definitions.Def_Formalism_HermitianCurvature_StatementLE
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ShiftBound
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DegreeOfProdLinearLe
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WeightedL2BoundedMul
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_Cauchy
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_Markov
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DerivedCoefficientIntegrable
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace Formalism.FourierDecayAlt.P.LEx2
open Formalism.FourierDecayAlt.LE
private theorem onBoxes_ofFn_of_mem_box (S : Formalism.FourierDecayAlt.LE.Sys) : ∀ (N : ℕ) (Y : Fin N → ℝ),
    (∀ a : Fin N, Y a ∈ S.box (N - 1 - (a : ℕ))) → S.OnBoxes (List.ofFn Y) := by
  intro N
  induction N with
  | zero =>
    intro Y _
    rw [List.ofFn_zero]
    exact trivial
  | succ N ih =>
    intro Y hY
    rw [List.ofFn_succ]
    show Y 0 ∈ S.box (List.ofFn fun i => Y i.succ).length ∧ S.OnBoxes (List.ofFn fun i => Y i.succ)
    refine ⟨?_, ih _ (fun i => ?_)⟩
    · convert hY 0 using 2
      simp only [List.length_ofFn, Fin.val_zero]
      omega
    · convert hY i.succ using 2
      simp only [Fin.val_succ]
      omega
private theorem degreeOf_prod_le_sum_degreeOf {σ ι : Type} (i : σ) (s : Finset ι) (f : ι → MvPolynomial σ ℝ) :
    MvPolynomial.degreeOf i (∏ j ∈ s, f j) ≤ ∑ j ∈ s, MvPolynomial.degreeOf i (f j) := by
  classical
  refine Finset.induction_on s ?_ ?_
  · rw [Finset.prod_empty, Finset.sum_empty, ← MvPolynomial.C_1, MvPolynomial.degreeOf_C]
  · intro a s ha ih
    rw [Finset.prod_insert ha, Finset.sum_insert ha]
    exact (MvPolynomial.degreeOf_mul_le _ _ _).trans (Nat.add_le_add_left ih _)
private theorem degreeOf_C_mul_prod_X_add_C_le (N m : ℕ) (c : ℝ) (lam : Fin m → ℝ) (i : Fin N) :
    MvPolynomial.degreeOf i (MvPolynomial.C c *
      ∏ a : Fin N, ∏ s : Fin m, (MvPolynomial.X a + MvPolynomial.C (lam s))) ≤ m := by
  classical
  refine (MvPolynomial.degreeOf_mul_le _ _ _).trans ?_
  rw [MvPolynomial.degreeOf_C, zero_add]
  refine (degreeOf_prod_le_sum_degreeOf i _ _).trans ?_
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i)]
  have h1 : ∑ a ∈ Finset.univ.erase i,
      MvPolynomial.degreeOf i (∏ s : Fin m, (MvPolynomial.X a + MvPolynomial.C (lam s))) = 0 := by
    refine Finset.sum_eq_zero (fun a ha => ?_)
    have hai : a ≠ i := Finset.ne_of_mem_erase ha
    refine Nat.eq_zero_of_le_zero ((degreeOf_prod_le_sum_degreeOf i _ _).trans (le_of_eq (Finset.sum_eq_zero (fun s _ => ?_))))
    refine Nat.eq_zero_of_le_zero ((MvPolynomial.degreeOf_add_le _ _ _).trans ?_)
    rw [MvPolynomial.degreeOf_X, MvPolynomial.degreeOf_C, if_neg (Ne.symm hai)]
    simp
  rw [h1, zero_add]
  refine (degreeOf_prod_le_sum_degreeOf i _ _).trans ?_
  calc ∑ s : Fin m, MvPolynomial.degreeOf i (MvPolynomial.X i + MvPolynomial.C (lam s))
      ≤ ∑ _s : Fin m, 1 := Finset.sum_le_sum (fun s _ => by
        refine (MvPolynomial.degreeOf_add_le _ _ _).trans ?_
        rw [MvPolynomial.degreeOf_X, MvPolynomial.degreeOf_C, if_pos rfl]
        simp)
    _ = m := by simp
private theorem le_reduceToBoxes_proof : Formalism.FourierDecayAlt.LE.ReduceToBoxes := by
  intro hGrid hSign hFit S hL hfit hRO hI1 hBox w hw hlen
  classical
  obtain ⟨sg0, -, hsg⟩ := hSign (S.k + 2 * S.r + 1) S.lam S.α S.β hRO
  obtain ⟨hmid, -, hadm⟩ := hFit S hL hfit
  have hL0 : 0 < S.L := by linarith
  suffices h : ∀ (N : ℕ) (sg : Fin N → Bool) (Y : Fin N → ℝ),
      S.admitted (List.ofFn fun a => (sg a, Y a)) → N ≤ S.Ntot →
      Filter.Tendsto (fun ε : ℝ => S.principalHermitianLattice ε (List.ofFn fun a => (sg a, Y a))) (nhdsWithin 0 (Set.Ioi 0))
        (nhds (S.size (List.ofFn fun a => (sg a, Y a)) * S.jn)) by
    have hwe : (List.ofFn fun a : Fin w.length => ((w.get a).1, (w.get a).2)) = w := by
      simp only [Prod.mk.eta]
      exact List.ofFn_get w
    have h' := h w.length (fun a => (w.get a).1) (fun a => (w.get a).2) (by rw [hwe]; exact hw) hlen
    rw [hwe] at h'
    exact h'
  intro N sg Y hadmY hN
  have hex : ∀ ε : ℝ, ∃ Q : MvPolynomial (Fin N) ℝ,
      (∀ a, Q.degreeOf a ≤ S.k + 2 * S.r + 1) ∧
      (0 < ε → ∀ (sg' : Fin N → Bool) (Y' : Fin N → ℝ), S.admitted (List.ofFn fun a => (sg' a, Y' a)) →
        S.principalHermitianLattice ε (List.ofFn fun a => (sg' a, Y' a)) = MvPolynomial.eval Y' Q) := by
    intro ε
    by_cases hε : 0 < ε
    · obtain ⟨Q, hQ1, hQ2⟩ := hI1 ε hε N hN
      exact ⟨Q, hQ1, fun _ => hQ2⟩
    · exact ⟨0, fun a => by simp, fun h => absurd h hε⟩
  choose Qf hQf using hex
  set Q₀ : MvPolynomial (Fin N) ℝ := MvPolynomial.C (sg0 ^ N * S.jn) *
    ∏ a : Fin N, ∏ s : Fin (S.k + 2 * S.r + 1), (MvPolynomial.X a + MvPolynomial.C (S.lam s)) with hQ₀
  have hdeg0 : ∀ a, Q₀.degreeOf a ≤ S.k + 2 * S.r + 1 := fun a => degreeOf_C_mul_prod_X_add_C_le _ _ _ _ a
  have hval : ∀ Y' : Fin N → ℝ, (∀ a, Y' a ∈ Set.Icc S.α S.β) → ∀ sg' : Fin N → Bool,
      S.size (List.ofFn fun a => (sg' a, Y' a)) * S.jn = MvPolynomial.eval Y' Q₀ := by
    intro Y' hY' sg'
    have habs : ∀ a, |S.P (Y' a)| = sg0 * ∏ s, (Y' a + S.lam s) := fun a => hsg (Y' a) (hY' a)
    simp only [Formalism.FourierDecayAlt.LE.Sys.size, List.map_ofFn, List.prod_ofFn, Function.comp_apply]
    rw [hQ₀]
    simp only [map_mul, map_prod, map_add, MvPolynomial.eval_C, MvPolynomial.eval_X]
    simp only [habs, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    ring
  have hc : (0:ℝ) < ((S.k + 2 * S.r + 1 : ℕ) : ℝ) + 1 := by positivity
  let grid : Fin N → Finset ℝ := fun a => (Finset.range (S.k + 2 * S.r + 1 + 1)).image
    (fun i : ℕ => S.α + (S.β - S.α) / 3 + 2 * ((N - 1 - (a : ℕ) : ℕ) : ℝ) * S.L +
      (i : ℝ) * (S.L / (((S.k + 2 * S.r + 1 : ℕ) : ℝ) + 1)))
  have hcard : ∀ a, (grid a).card = S.k + 2 * S.r + 1 + 1 := by
    intro a
    rw [Finset.card_image_of_injective _ (fun i j hij => by
      have hq : (0:ℝ) < S.L / (((S.k + 2 * S.r + 1 : ℕ) : ℝ) + 1) := div_pos hL0 hc
      have h2 := add_left_cancel hij
      exact_mod_cast mul_right_cancel₀ hq.ne' h2)]
    exact Finset.card_range _
  have hconv : ∀ Y' : Fin N → ℝ, (∀ a, Y' a ∈ grid a) →
      Filter.Tendsto (fun t => MvPolynomial.eval Y' (Qf t)) (nhdsWithin 0 (Set.Ioi 0))
        (nhds (MvPolynomial.eval Y' Q₀)) := by
    intro Y' hY'
    have hbox : ∀ a : Fin N, Y' a ∈ S.box (N - 1 - (a : ℕ)) := by
      intro a
      obtain ⟨i, hi, hiY⟩ := Finset.mem_image.mp (hY' a)
      rw [← hiY]
      have hi' : (i:ℝ) ≤ ((S.k + 2 * S.r + 1 : ℕ) : ℝ) := by
        exact_mod_cast (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))
      have h0 : 0 ≤ (i:ℝ) * (S.L / (((S.k + 2 * S.r + 1 : ℕ) : ℝ) + 1)) :=
        mul_nonneg (Nat.cast_nonneg _) (div_nonneg hL0.le hc.le)
      have h1 : (i:ℝ) * (S.L / (((S.k + 2 * S.r + 1 : ℕ) : ℝ) + 1)) ≤ S.L := by
        rw [mul_div_assoc', div_le_iff₀ hc]
        nlinarith [mul_le_mul_of_nonneg_right hi' hL0.le]
      constructor
      · linarith
      · linarith
    have hOnY : S.OnBoxes (List.ofFn Y') := onBoxes_ofFn_of_mem_box S N Y' hbox
    have hb := hBox (List.ofFn Y') hOnY (by rw [List.length_ofFn]; exact hN)
    have hplus : Formalism.FourierDecayAlt.LE.plus (List.ofFn Y') = List.ofFn fun a => (true, Y' a) := by
      simp only [Formalism.FourierDecayAlt.LE.plus, List.map_ofFn]
      rfl
    have hIcc : ∀ a, Y' a ∈ Set.Icc S.α S.β := fun a => by
      have ha := a.isLt
      have hm := hmid (N - 1 - (a : ℕ)) (by omega) (hbox a)
      have hαβ : S.α ≤ S.β := by linarith [hm.1, hm.2]
      exact ⟨by linarith [hm.1], by linarith [hm.2]⟩
    rw [hplus, hval Y' hIcc (fun _ => true)] at hb
    refine hb.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with ε hε
    have hA := hadm (List.ofFn Y') hOnY (by rw [List.length_ofFn]; exact hN)
    rw [hplus] at hA
    exact (hQf ε).2 hε (fun _ => true) Y' hA
  have hlim := hGrid N (S.k + 2 * S.r + 1) ℝ (nhdsWithin 0 (Set.Ioi 0)) Qf Q₀ grid
    (fun t a => (hQf t).1 a) hdeg0 hcard hconv Y
  obtain ⟨hA1, -⟩ := id hadmY
  have hIcc : ∀ a, Y a ∈ Set.Icc S.α S.β := fun a =>
    hA1 (sg a, Y a) (by simp only [List.mem_ofFn]; exact ⟨a, rfl⟩)
  rw [hval Y hIcc sg]
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact ((hQf ε).2 hε sg Y hadmY).symm
end Formalism.FourierDecayAlt.P.LEx2
end

set_option autoImplicit false

namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.LE.ReduceToBoxes := Formalism.FourierDecayAlt.P.LEx2.le_reduceToBoxes_proof
end Formalism.FourierDecayAlt.P
