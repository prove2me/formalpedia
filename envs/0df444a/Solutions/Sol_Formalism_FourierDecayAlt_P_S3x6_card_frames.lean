-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.S3x6.card_frames
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:20:32.399545+00:00
-- url     : https://prove2.me/submissions/ec449670-1520-49c5-accc-dc1ed82c108f

import Definitions.Def_Formalism_HermitianCurvature_MemParahoricTimesPrincipalCongruenceIff
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RestrictOrthogonalComplementNondeg
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x6_restrict_form_hermitian
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x6_restrict_orthogonal_complement_nondeg
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x6_finrank_orthogonal_unit_add_one
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x6_card_unit_norm_vectors

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
theorem _root_.solution (hσ : Inv σ) [Finite K] (s : ℕ → ℕ)
    (hs : ∀ n, Nat.card {w : Fin n → K // ∑ i, σ (w i) * w i = 1} = s n) (n : ℕ) :
    ∀ (V : Type) [AddCommGroup V] [Module K V] [FiniteDimensional K V] (h : V →ₛₗ[σ] V →ₗ[K] K),
    Herm h → Nondeg h → finrank K V = n →
    Nat.card {b : Fin n → V // Ortho h b} = ∏ j ∈ Finset.range n, s (j + 1) := by
  induction n with
  | zero =>
    intro V _ _ _ h _ _ _
    rw [Finset.prod_range_zero, Nat.card_eq_one_iff_unique]
    exact ⟨⟨fun a b => Subtype.ext (Subsingleton.elim _ _)⟩, ⟨⟨Fin.elim0, fun i => i.elim0⟩⟩⟩
  | succ n ih =>
    intro V _ _ _ h hh hn hfin
    have : Finite V := Module.finite_of_finite K
    let _ : Fintype {v : V // h v v = 1} := Fintype.ofFinite _
    rw [Nat.card_congr (orthonormalFrameEquiv hh n), Nat.card_sigma]
    have h1 : ∀ v : {v : V // h v v = 1},
        Nat.card {c : Fin n → LinearMap.ker (h v.1) // Ortho (restrictFormAlt h (LinearMap.ker (h v.1))) c} =
          ∏ j ∈ Finset.range n, s (j + 1) := by
      intro v
      have hW := finrank_orthogonal_unit_add_one h v.1 v.2
      exact ih (LinearMap.ker (h v.1)) (restrictFormAlt h _) (restrict_form_hermitian hh _)
        (restrict_orthogonal_complement_nondeg hh hn v.1 v.2) (by omega)
    rw [Finset.sum_congr rfl (fun v _ => h1 v), Finset.sum_const, Finset.card_univ,
      ← Nat.card_eq_fintype_card, card_unit_norm_vectors hσ s hs (n + 1) V h hh hn hfin,
      Finset.prod_range_succ, smul_eq_mul, mul_comm]
end Formalism.FourierDecayAlt.P.S3x6
