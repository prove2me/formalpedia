-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.off_diagonal_schur_complement
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:02:33.397837+00:00
-- url     : https://prove2.me/submissions/6f6ac238-ebee-46df-b658-b551c1edc2aa

import Definitions.Def_Formalism_HermitianCurvature_StatementTA
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OffDiagonalSchurComplement
import Theorems.Thm_Formalism_FourierDecayAlt_P_TA2_isPt_PT
import Theorems.Thm_Formalism_FourierDecayAlt_P_TA2_isPt_ext
import Theorems.Thm_Formalism_FourierDecayAlt_P_TA2_gram_nonneg
import Theorems.Thm_Formalism_FourierDecayAlt_P_TA2_psdOn_comp
import Theorems.Thm_Formalism_FourierDecayAlt_P_TA2_schur_abs
import Theorems.Thm_Formalism_FourierDecayAlt_P_TA2_mean_le_wsup

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt.TA Finset
open scoped ComplexConjugate InnerProductSpace
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.P.TA2
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.TA.OffDiagSchur := by
  classical
  intro E _ _ H _ _ W _ len Kl Nw D Sg Φ Pat3 _ pat3 c3 ep3 i s w hNZ hs hsi hi hK hA2 h73 hLat hw
  obtain ⟨th, hth, hest⟩ := h73 w hw
  have hHdPt : ∀ h ∈ PT Sg (i - s), IsPt (i - s) h := fun h hh => isPt_PT Sg hNZ _ h hh
  have hTnz : ∀ t ∈ Sg i s, t ≠ 0 := fun t ht => hNZ _ _ t ht
  have hPSD : PSDOn ((PT Sg (i - s) ×ˢ Sg i s).image fun x => ext x.1 s x.2) (D.K i) :=
    hK.2 i hi _ (by
      intro p hp
      simp only [mem_image, mem_product] at hp
      obtain ⟨x, ⟨h1, h2⟩, rfl⟩ := hp
      exact isPt_ext hs hsi (hHdPt _ h1) (hTnz _ h2))
  have hdiagPSD : ∀ t ∈ Sg i s, PSDOn (PT Sg (i - s)) (offK (D.K i) s t t) := by
    intro t ht
    refine psdOn_comp (fun h => ext h s t) List.dropLast (fun h => by simp [Formalism.FourierDecayAlt.TA.ext]) _ _
      (hK.2 i hi _ ?_)
    intro p hp
    simp only [mem_image] at hp
    obtain ⟨h, hh, rfl⟩ := hp
    exact isPt_ext hs hsi (hHdPt _ hh) (hTnz _ ht)
  have hest' := hest (PT Sg (i - s)) (D.K i) (Sg i s) hHdPt hTnz hPSD

  set N : E → E → ℂ := fun t t' => Nst (Φ w) (PT Sg (i - s)) (offK (D.K i) s t t') s t t' with hN
  set d : W → E → ℝ := fun w' t => (Nst (Φ w') (PT Sg (i - s)) (offK (D.K i) s t t) s t t).re with hd
  have hdnn : ∀ w', ∀ t ∈ Sg i s, 0 ≤ d w' t := fun w' t ht =>
    gram_nonneg (PT Sg (i - s)) (offK (D.K i) s t t) (fun h => Φ w' (ext h s t)) (hdiagPSD t ht)
  set c : E → E → ℝ := fun t t' =>
    if t ≠ t' ∧ 1 / t - 1 / t' ∈ D.Lf i s then c3 (1 / t - 1 / t') else 0 with hc
  set A : E → ℝ := fun t => ∑ π, ∑ x, th π x * d x.1 t with hA
  set B : E → ℝ := fun t => ∑ π, ∑ x, th π x * d x.2 t with hB
  have hAnn : ∀ t ∈ Sg i s, 0 ≤ A t := fun t ht =>
    sum_nonneg fun π _ => sum_nonneg fun x _ => mul_nonneg ((hth π).1 x) (hdnn _ t ht)
  have hBnn : ∀ t ∈ Sg i s, 0 ≤ B t := fun t ht =>
    sum_nonneg fun π _ => sum_nonneg fun x _ => mul_nonneg ((hth π).1 x) (hdnn _ t ht)
  have hep : 0 ≤ ep3 := by simpa using hLat.2 ∅ (by simp)

  have hoff : ∀ t ∈ Sg i s, ∀ t' ∈ Sg i s, t ≠ t' → (N t t').re ≤ c t t' * ((A t + B t') / 2) := by
    intro t ht t' ht' hne
    by_cases hl : 1 / t - 1 / t' ∈ D.Lf i s
    · have hcv : c t t' = c3 (1 / t - 1 / t') := if_pos ⟨hne, hl⟩
      rw [hcv]
      refine (Complex.re_le_norm _).trans ((hest' t ht t' ht' hne).trans ?_)
      refine mul_le_mul_of_nonneg_left ?_ (hLat.1 _)
      have e : (A t + B t') / 2 = ∑ π, ∑ x, th π x * ((d x.1 t + d x.2 t') / 2) := by
        simp only [hA, hB]
        rw [← sum_add_distrib, sum_div]
        refine sum_congr rfl fun π _ => ?_
        rw [← sum_add_distrib, sum_div]
        exact sum_congr rfl fun x _ => by ring
      rw [e]
      exact single_le_sum (f := fun π => ∑ x, th π x * ((d x.1 t + d x.2 t') / 2))
        (fun π _ => sum_nonneg fun x _ => mul_nonneg ((hth π).1 x)
          (by have := hdnn x.1 t ht; have := hdnn x.2 t' ht'; positivity)) (mem_univ (pat3 t t'))
    · have hcv : c t t' = 0 := if_neg fun h => hl h.2
      have hz : N t t' = 0 := by
        simp only [hN, Nst]
        refine sum_eq_zero fun h hh => sum_eq_zero fun h' hh' => ?_
        have := hA2 i s hs hsi hi h h' t t' (hHdPt h hh) (hHdPt h' hh') (hTnz t ht) (hTnz t' ht')
          (Or.inl hl)
        simp [offK, this]
      rw [hcv, hz]; simp

  have hrow : ∀ t ∈ Sg i s, ∑ t' ∈ Sg i s, c t t' ≤ ep3 := by
    intro t ht
    simp only [hc]
    rw [← sum_filter]
    have hinj : Set.InjOn (fun t' : E => 1 / t - 1 / t')
        ((Sg i s).filter fun t' => t ≠ t' ∧ 1 / t - 1 / t' ∈ D.Lf i s : Finset E) := by
      intro a _ b _ hab
      have : (1 : E) / a = 1 / b := by simpa using hab
      simpa using this
    rw [← sum_image (f := c3) hinj]
    refine hLat.2 _ ?_
    intro x hx
    simp only [mem_image, mem_filter] at hx
    obtain ⟨t', ⟨_, hne, hl⟩, rfl⟩ := hx
    refine ⟨hl, fun h0 => hne ?_⟩
    have : (1 : E) / t = 1 / t' := sub_eq_zero.mp h0
    simpa using this
  have hcol : ∀ t' ∈ Sg i s, ∑ t ∈ Sg i s, c t t' ≤ ep3 := by
    intro t' ht'
    simp only [hc]
    rw [← sum_filter]
    have hinj : Set.InjOn (fun t : E => 1 / t - 1 / t')
        ((Sg i s).filter fun t => t ≠ t' ∧ 1 / t - 1 / t' ∈ D.Lf i s : Finset E) := by
      intro a _ b _ hab
      have : (1 : E) / a = 1 / b := by simpa using hab
      simpa using this
    rw [← sum_image (f := c3) hinj]
    refine hLat.2 _ ?_
    intro x hx
    simp only [mem_image, mem_filter] at hx
    obtain ⟨t, ⟨_, hne, hl⟩, rfl⟩ := hx
    refine ⟨hl, fun h0 => hne ?_⟩
    have : (1 : E) / t = 1 / t' := sub_eq_zero.mp h0
    simpa using this
  have hschur := schur_abs (Sg i s) c A B ep3 hAnn hBnn hrow hcol

  set M : ℝ := wsup len (len w + Kl) (fun w' => Diag D Sg Φ w' i s) with hM
  have hDiag : ∀ w', Diag D Sg Φ w' i s = ∑ t ∈ Sg i s, d w' t := fun w' => rfl
  have hsumA : ∑ t ∈ Sg i s, A t ≤ Fintype.card Pat3 * M := by
    have e : ∑ t ∈ Sg i s, A t = ∑ π : Pat3, ∑ x, th π x * Diag D Sg Φ x.1 i s := by
      simp only [hA, hDiag]
      rw [sum_comm]
      refine sum_congr rfl fun π _ => ?_
      rw [sum_comm]
      exact sum_congr rfl fun x _ => (mul_sum _ _ _).symm
    rw [e]
    calc ∑ π : Pat3, ∑ x, th π x * Diag D Sg Φ x.1 i s ≤ ∑ _π : Pat3, M :=
          sum_le_sum fun π _ => (mean_le_wsup len _ (th π) (hth π) (fun w' => Diag D Sg Φ w' i s)).1
      _ = Fintype.card Pat3 * M := by simp
  have hsumB : ∑ t ∈ Sg i s, B t ≤ Fintype.card Pat3 * M := by
    have e : ∑ t ∈ Sg i s, B t = ∑ π : Pat3, ∑ x, th π x * Diag D Sg Φ x.2 i s := by
      simp only [hB, hDiag]
      rw [sum_comm]
      refine sum_congr rfl fun π _ => ?_
      rw [sum_comm]
      exact sum_congr rfl fun x _ => (mul_sum _ _ _).symm
    rw [e]
    calc ∑ π : Pat3, ∑ x, th π x * Diag D Sg Φ x.2 i s ≤ ∑ _π : Pat3, M :=
          sum_le_sum fun π _ => (mean_le_wsup len _ (th π) (hth π) (fun w' => Diag D Sg Φ w' i s)).2
      _ = Fintype.card Pat3 * M := by simp

  have hsplit : Ssplit D Sg Φ w i s = ∑ t ∈ Sg i s, ∑ t' ∈ Sg i s, (N t t').re := by
    simp only [Ssplit, hN, Complex.re_sum]
  have hterm : ∀ t ∈ Sg i s, ∑ t' ∈ Sg i s, (N t t').re
      ≤ d w t + ∑ t' ∈ Sg i s, c t t' * ((A t + B t') / 2) := by
    intro t ht
    have h1 : ∀ t' ∈ Sg i s, (N t t').re
        ≤ (if t = t' then d w t else 0) + c t t' * ((A t + B t') / 2) := by
      intro t' ht'
      by_cases hne : t = t'
      · subst hne
        simp [hc, hN, hd]
      · simpa [hne] using hoff t ht t' ht' hne
    refine (sum_le_sum h1).trans_eq ?_
    rw [sum_add_distrib, sum_ite_eq, if_pos ht]
  rw [hsplit, hDiag w]
  have h2 := sum_le_sum hterm
  rw [sum_add_distrib] at h2
  have h3 : ep3 * ((∑ t ∈ Sg i s, A t + ∑ t ∈ Sg i s, B t) / 2) ≤ Fintype.card Pat3 * ep3 * M := by
    have : (∑ t ∈ Sg i s, A t + ∑ t ∈ Sg i s, B t) / 2 ≤ Fintype.card Pat3 * M := by linarith
    calc _ ≤ ep3 * (Fintype.card Pat3 * M) := mul_le_mul_of_nonneg_left this hep
      _ = _ := by ring
  linarith
end Formalism.FourierDecayAlt.P
