-- Prove2me | solution 1 for Formalism.L2.Pj.linIndep_alg_pts
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T10:16:45.163808+00:00
-- url     : https://prove2.me/submissions/b76bb1e9-b890-4bd1-a21e-835854592948

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_AlgebraMapCAt
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ReadAlg
import Theorems.Thm_Formalism_L2_Pj_eq_zero_of_pts

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
theorem _root_.solution [CharZero K] {Kb : Type} [Field Kb] [IsAlgClosed Kb] [Algebra K Kb] [Normal K Kb] (p : TRing K) {m : ℕ} (a : Fin m → p.R)
    (ha : LinearIndependent K a) (v : Fin m → Kb)
    (h : ∀ φ : p.R →ₐ[K] Kb, ∑ i, v i * φ (a i) = 0) : v = 0 := by
  classical
  let L : IntermediateField K Kb := IntermediateField.adjoin K (Set.range v)
  haveI : FiniteDimensional K L :=
    IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x
  let u : Fin m → L := fun i => ⟨v i, IntermediateField.subset_adjoin K _ ⟨i, rfl⟩⟩
  have hu : ∀ i, algebraMap L Kb (u i) = v i := fun i => rfl

  have hg : ∀ (g : L →ₐ[K] Kb) (φ : p.R →ₐ[K] Kb), ∑ i, g (u i) * φ (a i) = 0 := by
    intro g φ
    let G : Kb →ₐ[K] Kb := g.liftNormal Kb
    have hb : Function.Bijective G := Algebra.IsAlgebraic.algHom_bijective G
    let Ge : Kb ≃ₐ[K] Kb := AlgEquiv.ofBijective G hb
    have h1 := h ((Ge.symm : Kb →ₐ[K] Kb).comp φ)
    have h2 := congrArg G h1
    rw [map_zero, map_sum] at h2
    refine Eq.trans ?_ h2
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, ← hu i, AlgHom.liftNormal_commutes]
    congr 1
    show φ (a i) = G (Ge.symm (φ (a i)))
    exact (Ge.apply_symm_apply (φ (a i))).symm

  have htr : ∀ lam : L, ∀ i, Algebra.trace K L (lam * u i) = 0 := by
    intro lam
    have hpt : ∀ φ : p.R →ₐ[K] Kb, φ (∑ i, Algebra.trace K L (lam * u i) • a i) = 0 := by
      intro φ
      rw [map_sum]
      have : ∀ i, φ (Algebra.trace K L (lam * u i) • a i) =
          (∑ g : L →ₐ[K] Kb, g (lam * u i)) * φ (a i) := by
        intro i
        rw [map_smul, Algebra.smul_def, ← trace_eq_sum_embeddings]
      simp_rw [this, Finset.sum_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_eq_zero fun g _ => ?_
      have := hg g φ
      calc ∑ i, g (lam * u i) * φ (a i) = g lam * ∑ i, g (u i) * φ (a i) := by
            rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun i _ => ?_; rw [map_mul, mul_assoc]
        _ = 0 := by rw [this, mul_zero]
    have h0 := eq_zero_of_pts p _ hpt
    exact fun i => (Fintype.linearIndependent_iff.1 ha _ h0) i
  funext i
  have hz : u i = 0 := by
    refine (traceForm_nondegenerate K L).1 (u i) fun lam => ?_
    rw [Algebra.traceForm_apply, mul_comm]
    exact htr lam i
  rw [← hu i, hz, map_zero]
  rfl
end Formalism.L2.Pj
