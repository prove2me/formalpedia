-- Prove2me | solution 1 for Formalism.L2.Pj.linIndep_cpts
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T10:23:44.821625+00:00
-- url     : https://prove2.me/submissions/a7b3d76d-29a7-46c4-b1ea-9c2e709d1c6f

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_AlgebraMapCAt
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ReadAlg
import Theorems.Thm_Formalism_L2_Pj_linIndep_alg_pts

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Pj
open MvPolynomial
variable {K : Type} [Field K]
namespace Formalism.L2.Pj
theorem _root_.solution [CharZero K] (σ : K →+* ℂ) (p : TRing K) {m : ℕ} (a : Fin m → p.R)
    (ha : LinearIndependent K a) (w : Fin m → ℂ)
    (h : ∀ ψ : p.R →ₐ[K] CAt σ, ∑ i, w i * cvalR σ (ψ (a i)) = 0) : w = 0 := by
  classical
  letI : Algebra K ℂ := σ.toAlgebra
  let ι : AlgebraicClosure K →ₐ[K] ℂ := IsAlgClosed.lift
  let Kb := AlgebraicClosure K
  letI : Module Kb ℂ := Module.compHom ℂ (ι.toRingHom : Kb →+* ℂ)
  have hsm : ∀ (c : Kb) (z : ℂ), c • z = ι c * z := fun _ _ => rfl
  by_contra hw
  obtain ⟨j, hj⟩ : ∃ j, w j ≠ 0 := by
    by_contra hne
    push Not at hne
    exact hw (funext hne)
  obtain ⟨ℓ, hℓ⟩ : ∃ ℓ : Module.Dual Kb ℂ, ℓ (w j) ≠ 0 := by
    by_contra hne
    push Not at hne
    exact hj ((Module.forall_dual_apply_eq_zero_iff Kb (w j)).1 hne)
  have hv := linIndep_alg_pts (Kb := AlgebraicClosure K) p a ha (fun i => ℓ (w i)) fun φ => by
    have h1 := congrArg ℓ (h (ι.comp φ : p.R →ₐ[K] ℂ))
    rw [map_zero, map_sum] at h1
    refine Eq.trans ?_ h1
    refine Finset.sum_congr rfl fun i _ => ?_
    have e : w i * cvalR σ ((ι.comp φ : p.R →ₐ[K] ℂ) (a i)) = φ (a i) • w i := by
      rw [hsm, mul_comm]; rfl
    erw [e, map_smul, smul_eq_mul, mul_comm]
  exact hℓ (congrFun hv j)
end Formalism.L2.Pj
