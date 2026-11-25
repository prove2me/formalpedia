-- Prove2me | solution 1 for Formalism.HC.Der.norm_mu
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T03:47:44.419168+00:00
-- url     : https://prove2.me/submissions/cce66bac-f323-4101-824f-0487dbeffed6

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_KcBase
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_KcEqOfPowEqOne
import Theorems.Thm_Formalism_HC_Der_kc_iod_fix
import Theorems.Thm_Formalism_HC_Der_kc_conj_mul_self
import Theorems.Thm_Formalism_FrobeniusOrbits_Final_conj
import Theorems.Thm_Formalism_HC_Der_kc_fixK
import Theorems.Thm_Formalism_HC_Der_kc_gal_conj


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IntermediateField Ideal
open scoped Pointwise nonZeroDivisors
noncomputable section
open Formalism Formalism.HC Formalism.HC.Der
open Formalism.FrobeniusOrbits Formalism.TwoAdicCyclotomicDecomposition
variable {φ : Frame} (H : HostRaw φ)
variable (C : HostCore H)
include C
namespace Formalism.HC.Der
theorem _root_.solution : ∀ x : H.E, (∃ m : ℕ, 0 < m ∧ x ^ m = 1) → Algebra.norm H.K x = 1 := by
  classical
  intro x hx
  have := H.galois
  have : IsGalois H.K H.E := IsGalois.tower_top_of_isGalois ℚ _ _
  obtain ⟨ι, hι⟩ := H.gal.surjective φ.iod
  set s₀ := H.conj * ι with hs₀
  have hg : H.gal s₀ = φ.sg := by
    rw [hs₀, map_mul, kc_gal_conj, hι]
    exact Prod.ext (show c0 * ((1, -1) : G0) = (-1, 1) by decide) (mul_one _)
  have hΨ : H.gal s₀ ∈ φ.Psi := by rw [hg]; rfl
  let s : H.E ≃ₐ[H.K] H.E := AlgEquiv.ofRingEquiv (f := s₀.toRingEquiv) (fun y => kc_fixK H s₀ hΨ y)
  have hs : ∀ y, s y = s₀ y := fun _ => rfl
  have hsx : x * s x = 1 := by
    rw [hs, hs₀, AlgEquiv.mul_apply, kc_iod_fix H C ι hι x hx]
    exact kc_conj_mul_self H C x hx
  have hss0 : s₀ * s₀ = 1 := by
    apply H.gal.injective
    rw [map_mul, hg, map_one]
    exact Prod.ext (show ((-1, 1) : G0) * (-1, 1) = 1 by decide) (mul_one _)
  have hss : s * s = 1 := AlgEquiv.ext fun y => DFunLike.congr_fun hss0 y
  have hs1 : s ≠ 1 := by
    intro h1
    have h2 : s₀ = 1 := AlgEquiv.ext fun y => DFunLike.congr_fun h1 y
    rw [h2, map_one] at hg
    exact absurd (congrArg (fun g : φ.GG => g.1) hg) (show ¬ (1 : G0) = (-1, 1) by decide)
  apply (algebraMap H.K H.E).injective
  rw [Algebra.norm_eq_prod_automorphisms, map_one]
  refine Finset.prod_involution (fun σ _ => σ * s) (fun σ _ => ?_) (fun σ _ _ => ?_) (fun _ _ => Finset.mem_univ _)
    (fun σ _ => ?_)
  · rw [AlgEquiv.mul_apply, ← map_mul, hsx, map_one]
  · exact fun h1 => hs1 (mul_eq_left.mp h1)
  · rw [mul_assoc, hss, mul_one]
end Formalism.HC.Der
