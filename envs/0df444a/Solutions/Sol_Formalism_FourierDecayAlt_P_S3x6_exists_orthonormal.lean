-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.S3x6.exists_orthonormal
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:09:30.428896+00:00
-- url     : https://prove2.me/submissions/83963bbb-d599-4186-a704-7b5e9be4e104

import Definitions.Def_Formalism_HermitianCurvature_MemParahoricTimesPrincipalCongruenceIff
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RestrictOrthogonalComplementNondeg
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x6_restrict_form_hermitian
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x6_restrict_orthogonal_complement_nondeg
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x6_finrank_orthogonal_unit_add_one
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x6_exists_unit_norm_vector

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.S3x6
open Module
variable {K : Type} [Field K] {σ : K →+* K}
namespace Formalism.FourierDecayAlt.P.S3x6
theorem _root_.solution (hσ : Inv σ) (n : ℕ) : ∀ (V : Type) [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (h : V →ₛₗ[σ] V →ₗ[K] K), Herm h → Nondeg h → finrank K V = n →
    ∃ b : Basis (Fin n) K V, Ortho h b := by
  induction n with
  | zero =>
    intro V _ _ _ h _ _ hfin
    exact ⟨finBasisOfFinrankEq K V hfin, fun i => i.elim0⟩
  | succ n ih =>
    intro V _ _ _ h hh hn hfin
    have hnt : Nontrivial V := Module.nontrivial_of_finrank_pos (R := K) (by omega)
    obtain ⟨u, hu⟩ := exists_ne (0 : V)
    have hne : ∃ u v, h u v ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact hu (hn u (hcon u))
    obtain ⟨v, hv⟩ := exists_unit_norm_vector hσ hh hne
    have hW := finrank_orthogonal_unit_add_one h v hv
    obtain ⟨bW, hbW⟩ := ih (LinearMap.ker (h v)) (restrictFormAlt h _) (restrict_form_hermitian hh _)
      (restrict_orthogonal_complement_nondeg hh hn v hv) (by omega)
    refine ⟨Basis.mkFinCons v bW ?_ ?_, ?_⟩
    · intro c x hx hc
      have := congrArg (h v) hc
      rw [LinearMap.mem_ker] at hx
      simpa [hv, hx] using this
    · intro z
      exact ⟨-(h v z), by simp [LinearMap.mem_ker, hv]⟩
    · rw [Basis.coe_mkFinCons, orthonormal_cons_iff hh]
      refine ⟨hv, fun i => ?_, fun i j => hbW i j⟩
      exact LinearMap.mem_ker.1 (bW i).2
end Formalism.FourierDecayAlt.P.S3x6
