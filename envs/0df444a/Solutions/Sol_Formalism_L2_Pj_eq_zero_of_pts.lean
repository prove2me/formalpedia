-- Prove2me | solution 1 for Formalism.L2.Pj.eq_zero_of_pts
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:57:55.789678+00:00
-- url     : https://prove2.me/submissions/500c4be9-8837-4726-b667-14d7417a57cc

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_AlgebraMapCAt
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ReadAlg

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
theorem _root_.solution {M : Type} [Field M] [IsAlgClosed M] [Algebra K M] (p : TRing K) (a : p.R)
    (h : ∀ ψ : p.R →ₐ[K] M, ψ a = 0) : a = 0 := by
  classical
  have hRdef : p.R = (MvPolynomial (Fin p.n) K ⧸ p.I) := rfl
  haveI : IsReduced p.R := (Ideal.isRadical_iff_quotient_reduced p.I).1 p.rad
  haveI : IsJacobsonRing p.R := inferInstanceAs (IsJacobsonRing (MvPolynomial (Fin p.n) K ⧸ p.I))
  haveI hFT : Algebra.FiniteType K p.R :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ K p.I) (Ideal.Quotient.mkₐ_surjective K p.I)
  have hrad : (⊥ : Ideal p.R).IsRadical := fun x ⟨k, hk⟩ =>
    (Submodule.mem_bot _).2 (IsNilpotent.eq_zero ⟨k, (Submodule.mem_bot _).1 hk⟩)
  have hjac : (⊥ : Ideal p.R).jacobson = ⊥ := by
    first
    | exact IsJacobsonRing.out inferInstance hrad
    | exact IsJacobsonRing.out' ⊥ hrad
  have ha : a ∈ (⊥ : Ideal p.R).jacobson := by
    set_option synthInstance.maxHeartbeats 400000 in
    refine Ideal.mem_sInf.2 fun J hJ => ?_
    have hJm : J.IsMaximal := hJ.2
    letI := Ideal.Quotient.field J
    haveI : Algebra.FiniteType K (p.R ⧸ J) :=
      Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ K J) (Ideal.Quotient.mkₐ_surjective K J)
    haveI : Module.Finite K (p.R ⧸ J) := finite_of_finite_type_of_isJacobsonRing K (p.R ⧸ J)
    haveI : Algebra.IsIntegral K (p.R ⧸ J) := Algebra.IsIntegral.of_finite K _
    haveI : Algebra.IsAlgebraic K (p.R ⧸ J) := Algebra.IsIntegral.isAlgebraic
    let ι : (p.R ⧸ J) →ₐ[K] M := IsAlgClosed.lift
    have h0 := h (ι.comp (Ideal.Quotient.mkₐ K J))
    have h1 : ι (Ideal.Quotient.mk J a) = ι 0 := by
      rw [map_zero]
      exact h0
    exact Ideal.Quotient.eq_zero_iff_mem.1 (ι.toRingHom.injective h1)
  rw [hjac] at ha
  exact (Submodule.mem_bot _).1 ha
end Formalism.L2.Pj
