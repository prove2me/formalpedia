-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.cosets_last_block_size_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:59:29.696276+00:00
-- url     : https://prove2.me/submissions/c9545c22-0d86-44c2-94de-225b0f1feb80

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_StatementTA
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GramConjugationNorm
import Theorems.Thm_Formalism_FourierDecayAlt_P_GramConjugationNorm_isPt_PT
import Theorems.Thm_Formalism_FourierDecayAlt_P_GramConjugationNorm_gram_re_nonneg
import Theorems.Thm_Formalism_FourierDecayAlt_P_GramConjugationNorm_gram_norm
import Theorems.Thm_Formalism_FourierDecayAlt_P_GramConjugationNorm_gram_dom
import Theorems.Thm_Formalism_FourierDecayAlt_P_GramConjugationNorm_avg_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Finset Filter Topology Formalism.FourierDecayAlt.TA Formalism.FourierDecayAlt.P.GramConjugationNorm
open scoped InnerProductSpace ComplexConjugate
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.TA.CosetsOne := by
  intro E _ _ H _ _ W _ len Kl Nw D Sg Φ tr Pat1 pat1 c1 ep1 i w R hNZ hi hir hK hA hE hP hEst hLat
    hw hR
  classical
  obtain ⟨th, hth, hest⟩ := hEst w hw
  obtain ⟨hA1, -, -, hA4⟩ := hA i 1 le_rfl hi hir
  have hHd : ∀ h ∈ PT Sg (i - 1), IsPt (i - 1) h := isPt_PT Sg hNZ _
  have he : 0 ≤ 1 + D.e i := by have := (hE i hi hir).1; linarith
  set Hd := PT Sg (i - 1) with hHdd
  set g : E → W → ℝ := fun t0 w' => (gram (D.Th i 1 t0) (Φ w') Hd).re with hg
  have hg0 : ∀ t0 w', 0 ≤ g t0 w' := fun t0 w' => gram_re_nonneg _ _ _ (hA1 t0 Hd hHd)
  have hdom : ∀ w', ∑ t0 ∈ R, g t0 w' ≤ (1 + D.e i) * Slev D Sg Φ w' (i - 1) :=
    fun w' => gram_dom R (1 + D.e i) (D.K (i - 1)) (D.Th i 1) (Φ w') _ (hA4 R _ hR hHd)
  set M : ℝ := wsup len (len w + Kl) (fun w' => Slev D Sg Φ w' (i - 1)) with hM
  have hM0 : 0 ≤ M :=
    Real.iSup_nonneg fun w' => gram_re_nonneg _ _ _ (hK.2 (i - 1) (by omega) Hd hHd)
  have hC0 : 0 ≤ (1 + D.e i) * M := mul_nonneg he hM0

  let f : E → E → ℝ := fun t0 l =>
    if l ∈ D.Lv i ∧ l ≠ 0 then c1 l * ∑ w', th (pat1 l) w' * g t0 w' else 0
  have hf0 : ∀ t0 l, 0 ≤ f t0 l := by
    intro t0 l
    simp only [f]
    split_ifs
    · exact mul_nonneg (hLat.1 l)
        (Finset.sum_nonneg fun w' _ => mul_nonneg ((hth _).1 w') (hg0 t0 w'))
    · exact le_rfl
  have hsumf : ∀ l, ∑ t0 ∈ R, f t0 l ≤
      if l ∈ D.Lv i ∧ l ≠ 0 then c1 l * ((1 + D.e i) * M) else 0 := by
    intro l
    simp only [f]
    split_ifs with h
    · rw [← Finset.mul_sum]
      exact mul_le_mul_of_nonneg_left
        (avg_le R len (len w + Kl) (th (pat1 l)) (hth _) g _ _ he hdom) (hLat.1 l)
    · simp
  have hpart : ∀ u : Finset E, ∑ l ∈ u, ∑ t0 ∈ R, f t0 l ≤ ep1 * ((1 + D.e i) * M) := by
    intro u
    calc ∑ l ∈ u, ∑ t0 ∈ R, f t0 l
        ≤ ∑ l ∈ u, if l ∈ D.Lv i ∧ l ≠ 0 then c1 l * ((1 + D.e i) * M) else 0 :=
          Finset.sum_le_sum fun l _ => hsumf l
      _ = (∑ l ∈ u.filter (fun l => l ∈ D.Lv i ∧ l ≠ 0), c1 l) * ((1 + D.e i) * M) := by
          rw [← Finset.sum_filter, Finset.sum_mul]
      _ ≤ ep1 * ((1 + D.e i) * M) :=
          mul_le_mul_of_nonneg_right
            (hLat.2 _ fun x hx => (Finset.mem_filter.1 hx).2) hC0
  have hsummable : ∀ t0 ∈ R, Summable (f t0) := by
    intro t0 ht0
    refine summable_of_sum_le (hf0 t0) (c := ep1 * ((1 + D.e i) * M)) fun u => ?_
    refine le_trans (Finset.sum_le_sum fun l _ => ?_) (hpart u)
    exact Finset.single_le_sum (f := fun t => f t l) (fun t _ => hf0 t l) ht0
  have hcls : ∀ t0 ∈ R, ∑ t ∈ (Sg i 1).filter (fun t => t - t0 ∈ D.La i 1),
      (Nst (Φ w) Hd (D.Th i 1 t0) 1 t t).re ≤ g t0 w + ∑' l, f t0 l := by
    intro t0 ht0
    have hpsd := hA1 t0 Hd hHd
    obtain ⟨h0, hl⟩ := hest Hd (D.Th i 1 t0) hHd hpsd
    have := hP w Hd (D.Th i 1 t0) hHd hpsd t0 ((Sg i 1).filter (fun t => t - t0 ∈ D.La i 1))
      (fun t ht => by rw [Finset.mem_filter] at ht; exact ⟨hNZ _ _ t ht.1, ht.2⟩)
      (∑' l, f t0 l) (fun L hL => by
        calc ∑ l ∈ L, ‖tr w Hd (D.Th i 1 t0) l‖ ≤ ∑ l ∈ L, f t0 l := by
              refine Finset.sum_le_sum fun l hlL => ?_
              simp only [f, if_pos (hL l hlL)]
              exact hl l (hL l hlL).1 (hL l hlL).2
          _ ≤ ∑' l, f t0 l := (hsummable t0 ht0).sum_le_tsum L (fun l _ => hf0 t0 l))
    rwa [h0, gram_norm _ _ _ hpsd] at this
  have htsum : ∑ t0 ∈ R, ∑' l, f t0 l ≤ ep1 * ((1 + D.e i) * M) := by
    rw [← Summable.tsum_finsetSum hsummable]
    exact Real.tsum_le_of_sum_le (fun l => Finset.sum_nonneg fun t0 _ => hf0 t0 l) hpart
  calc Cosets D Sg Φ w i 1 R ≤ ∑ t0 ∈ R, (g t0 w + ∑' l, f t0 l) := by
        unfold Cosets
        refine Finset.sum_le_sum fun t0 ht0 => ?_
        convert hcls t0 ht0
    _ = ∑ t0 ∈ R, g t0 w + ∑ t0 ∈ R, ∑' l, f t0 l := Finset.sum_add_distrib
    _ ≤ (1 + D.e i) * Slev D Sg Φ w (i - 1) + ep1 * ((1 + D.e i) * M) :=
        add_le_add (hdom w) htsum
    _ = _ := by ring
end Formalism.FourierDecayAlt.P
