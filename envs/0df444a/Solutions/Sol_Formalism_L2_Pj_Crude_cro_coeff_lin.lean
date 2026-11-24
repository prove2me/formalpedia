-- Prove2me | solution 1 for Formalism.L2.Pj.Crude.cro_coeff_lin
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T10:20:10.448794+00:00
-- url     : https://prove2.me/submissions/a8588321-0663-4c76-899e-d46be5009508

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_CrudeBase
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_CrudeOrd
import Theorems.Thm_Formalism_L2_Pj_Crude_cro_prod_monomial
import Theorems.Thm_Formalism_L2_Pj_IsEval_zero


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Pj Formalism.L2.Pj.Crude
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
variable {k : Type} [CommRing k] {d n : ℕ}
namespace Formalism.L2.Pj.Crude
theorem _root_.solution (G : FGLaw k d) (i j : Fin d) :
    coeff (Finsupp.single ((1 : Fin 2), i) 1) (G.F j) = if i = j then 1 else 0 := by
  have hu := congrArg (coeff (Finsupp.single ((0 : Fin 1), i) 1)) (G.unit j)
  rw [MvPowerSeries.coeff_X] at hu
  have hrhs : (if Finsupp.single ((0 : Fin 1), i) 1 = Finsupp.single ((0 : Fin 1), j) 1 then (1 : k) else 0) =
      if i = j then 1 else 0 := by
    by_cases hij : i = j
    · simp [hij]
    · rw [if_neg hij, if_neg]
      intro hs
      apply hij
      have h2 := congrArg (fun D : Fin 1 × Fin d →₀ ℕ => D ((0 : Fin 1), i)) hs
      simp [Finsupp.single_apply] at h2
      first
        | exact h2.symm
        | exact h2
  rw [hrhs] at hu
  rw [← hu]
  unfold ev
  have hc0 : ∀ p : Fin 2 × Fin d,
      constantCoeff ((![0, pt k d 0] : Fin 2 → Pt k 1 d) p.1 p.2) = 0 := by
    rintro ⟨p1, p2⟩
    fin_cases p1 <;> simp [pt]
  have ha : MvPowerSeries.HasSubst
      (fun p : Fin 2 × Fin d => (![0, pt k d 0] : Fin 2 → Pt k 1 d) p.1 p.2) := by
    first
      | exact MvPowerSeries.hasSubst_of_constantCoeff_zero hc0
      | exact MvPowerSeries.HasSubst.of_constantCoeff_nilpotent (fun p => by rw [hc0 p]; exact IsNilpotent.zero)
      | exact MvPowerSeries.hasSubst_of_constantCoeff_nilpotent (fun p => by rw [hc0 p]; exact IsNilpotent.zero)
  rw [MvPowerSeries.coeff_subst ha, finsum_eq_single _ (Finsupp.single ((1 : Fin 2), i) 1)]
  · rw [Finsupp.prod_single_index (by simp)]
    simp [pt, MvPowerSeries.coeff_X]
  · intro D hD
    suffices hc : coeff (Finsupp.single ((0 : Fin 1), i) 1)
        (D.prod fun s m => (fun p : Fin 2 × Fin d => (![0, pt k d 0] : Fin 2 → Pt k 1 d) p.1 p.2) s ^ m) = 0 by
      rw [hc, smul_zero]
    by_cases hx : ∃ s ∈ D.support, s.1 = 0
    · obtain ⟨⟨s1, s2⟩, hs, hs0⟩ := hx
      have hz : (D.prod fun s m =>
          (fun p : Fin 2 × Fin d => (![0, pt k d 0] : Fin 2 → Pt k 1 d) p.1 p.2) s ^ m) = 0 := by
        rw [Finsupp.prod]
        apply Finset.prod_eq_zero hs
        simp only at hs0
        subst hs0
        simp [zero_pow (Finsupp.mem_support_iff.mp hs)]
      rw [hz, map_zero]
    · push_neg at hx
      have hprod : (D.prod fun s m =>
          (fun p : Fin 2 × Fin d => (![0, pt k d 0] : Fin 2 → Pt k 1 d) p.1 p.2) s ^ m) =
          monomial (∑ s ∈ D.support, Finsupp.single ((0 : Fin 1), s.2) (D s)) (1 : k) := by
        rw [Finsupp.prod, ← cro_prod_monomial]
        refine Finset.prod_congr rfl fun s hs => ?_
        obtain ⟨s1, s2⟩ := s
        have h1 : s1 = 1 := by
          have := hx _ hs
          fin_cases s1
          · exact absurd rfl this
          · rfl
        subst h1
        first
          | simp [pt, MvPowerSeries.X_pow_eq]
          | simp [pt, MvPowerSeries.X, MvPowerSeries.monomial_pow]
      rw [hprod, MvPowerSeries.coeff_monomial, if_neg]
      intro heq
      apply hD
      ext ⟨s1, s2⟩
      have hev := congrArg (fun D' : Fin 1 × Fin d →₀ ℕ => D' ((0 : Fin 1), s2)) heq
      simp only [Finsupp.finset_sum_apply, Finsupp.single_apply, Prod.mk.injEq, true_and] at hev
      rw [Finset.sum_eq_single ((1 : Fin 2), s2)] at hev
      · fin_cases s1
        · have h0 : D ((0 : Fin 2), s2) = 0 := by
            by_contra hne
            exact hx _ (Finsupp.mem_support_iff.mpr hne) rfl
          simp [h0, Finsupp.single_apply]
        · simp [Finsupp.single_apply] at hev ⊢
          split_ifs at hev ⊢ <;> omega
      · intro s hs hne
        rw [if_neg]
        intro h2
        apply hne
        obtain ⟨t1, t2⟩ := s
        have := hx _ hs
        simp only at h2 this
        subst h2
        fin_cases t1
        · exact absurd rfl this
        · rfl
      · intro hnot
        have h0 : D ((1 : Fin 2), s2) = 0 := by simpa using hnot
        simp [h0]
end Formalism.L2.Pj.Crude
