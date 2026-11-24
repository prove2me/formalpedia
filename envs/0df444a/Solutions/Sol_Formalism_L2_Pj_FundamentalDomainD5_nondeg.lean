-- Prove2me | solution 1 for Formalism.L2.Pj.FundamentalDomainD5.nondeg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T10:23:59.592636+00:00
-- url     : https://prove2.me/submissions/cc28cfa7-09f3-487e-8718-ff98ce380cc0

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ArchimedeanQuadraticData_HQsmulRight
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ArchimedeanQuadraticData_FinrankCmType
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ArchimedeanQuadraticData_ThetaDotSelf
import Theorems.Thm_Formalism_L2_Pj_FundamentalDomainD5_trace_one_ne

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
open Formalism Formalism.L2 Formalism.L2.Pj Formalism.L2.Pj.FundamentalDomainD5
open NumberField Matrix ComplexConjugate ReciprocityTheory.MultiplicativeHeights
variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι] {r : ℕ}
namespace Formalism.L2.Pj.FundamentalDomainD5
theorem _root_.solution [Nonempty ι] (σ : ι → K →+* ℂ) (Q : ι → Matrix (Fin r) (Fin r) ℂ)
    (hQ : ∀ i, (Q i).det ≠ 0) (p : ℕ) (S : HermForm K r)
    (hform : ∀ i x y, σ i (S.h x y) = jForm p (Q i *ᵥ embVec (σ i) x) (Q i *ᵥ embVec (σ i) y))
    (x : Fin r → K) (h : ∀ v, Algebra.trace ℚ K (S.h v x) = 0) : x = 0 := by
  classical
  unfold jForm embVec at hform
  obtain ⟨i₀⟩ := ‹Nonempty ι›
  have hsingle : ∀ (j : Fin r) (b : K),
      (fun a => σ i₀ ((Pi.single j b : Fin r → K) a)) = (Pi.single j (σ i₀ b) : Fin r → ℂ) := by
    intro j b
    funext a
    by_cases ha : a = j
    · subst ha
      simp
    · simp [Pi.single_eq_of_ne ha]
  have hcol : ∀ (j : Fin r) (z : ℂ) (k : Fin r), (Q i₀ *ᵥ (Pi.single j z : Fin r → ℂ)) k = Q i₀ k j * z := by
    intro j z k
    simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  have hg : ∀ j : Fin r, S.h (Pi.single j 1) x = 0 := by
    intro j
    have hlin : ∀ b : K, S.h (Pi.single j b) x = S.1 b * S.h (Pi.single j 1) x := by
      intro b
      apply (σ i₀).injective
      rw [map_mul, hform, hform, hsingle, hsingle, S.3, Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [hcol, hcol, map_one]
      simp only [map_mul, map_one]
      ring
    by_contra hg0
    have ht := h (Pi.single j (S.1 (S.h (Pi.single j 1) x)⁻¹))
    have ht2 := hlin (S.1 (S.h (Pi.single j 1) x)⁻¹)
    rw [ht2, S.2, inv_mul_cancel₀ hg0] at ht
    exact trace_one_ne ht
  have hw : (Q i₀)ᴴ *ᵥ (fun k => sgn p k * (Q i₀ *ᵥ fun a => σ i₀ (x a)) k) = 0 := by
    funext j
    have h0 := congrArg (σ i₀) (hg j)
    rw [hform, hsingle, map_zero] at h0
    show ∑ k, (Q i₀)ᴴ j k * (sgn p k * (Q i₀ *ᵥ fun a => σ i₀ (x a)) k) = 0
    rw [← h0]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hcol, map_one, mul_one, Matrix.conjTranspose_apply, starRingEnd_apply]
    ring
  have hdet : ((Q i₀)ᴴ).det ≠ 0 := by
    rw [Matrix.det_conjTranspose]
    exact star_ne_zero.mpr (hQ i₀)
  have hw0 := Matrix.eq_zero_of_mulVec_eq_zero hdet hw
  have hu0 : (Q i₀ *ᵥ fun a => σ i₀ (x a)) = 0 := by
    funext k
    have hk := congrFun hw0 k
    simp only [Pi.zero_apply] at hk ⊢
    rcases mul_eq_zero.mp hk with hk | hk
    · unfold sgn at hk
      split_ifs at hk <;> norm_num at hk
    · exact hk
  have hx0 := Matrix.eq_zero_of_mulVec_eq_zero (hQ i₀) hu0
  funext a
  have ha := congrFun hx0 a
  simp only [Pi.zero_apply] at ha ⊢
  exact (σ i₀).injective (by rw [ha, map_zero])
end Formalism.L2.Pj.FundamentalDomainD5
