-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.PW.QQ_int
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T10:35:25.134505+00:00
-- url     : https://prove2.me/submissions/2e49ac3c-c287-4705-bd8c-dc88966afc27

import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_StatementB
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_HomRelationHolds
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_InvInt
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_TypeInt
import Theorems.Thm_Formalism_InvariantFactorPaths_PW_glRel_ofT
import Theorems.Thm_Formalism_InvariantFactorPaths_PW_weightZeroProj_mem_homLat
import Theorems.Thm_Formalism_InvariantFactorPaths_PW_QQ_apply
import Theorems.Thm_Formalism_InvariantFactorPaths_PW_hom_divided_holds
import Theorems.Thm_Formalism_InvariantFactorPaths_PW_hom_relation_holds
import Theorems.Thm_Formalism_InvariantFactorPaths_PW_invariant_integral_holds


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.PW
open Finset Formalism.GM.DimensionMonotonicity Formalism.CountingSumsFrames
variable (p : ℕ) [Fact p.Prime] {U V : Type} [AddCommGroup U] [Module ℚ_[p] U] [AddCommGroup V] [Module ℚ_[p] V]
  {n : ℕ}
namespace Formalism.InvariantFactorPaths.PW
theorem _root_.solution (G₁ : GlW ℚ_[p] U n) (G₂ : GlW ℚ_[p] V n) (S : Finset (Fin n → ℤ)) (l : ℕ) {k : ℕ}
    (b : Module.Basis (Fin k) ℚ_[p] U) {L : AddSubgroup U} {M : AddSubgroup V} (hZ : ZpClosed p M)
    (hLd : DivStable G₁.E L) (hMd : DivStable G₂.E M) (hLg : ∀ μ, ∀ x ∈ L, G₁.comp μ x ∈ L)
    (hMg : ∀ μ, ∀ x ∈ M, G₂.comp μ x ∈ M) (hbL : ∀ i, b i ∈ L) (hbi : ∀ x ∈ L, ∀ i, ‖b.repr x i‖ ≤ 1)
    {m : V} (hm : m ∈ M) :
    ((p : ℚ_[p]) ^ (n.choose 2 * Nat.log p (l + n - 1))) • QQ G₁ G₂ S l b m ∈ M := by
  obtain ⟨hZH, hDH⟩ := hom_divided_holds p U V (Fin n) G₁.E G₂.E L M hZ hLd hMd
  have hrel : GlRel (homAct G₁.E G₂.E) :=
    hom_relation_holds ℚ_[p] U V (Fin n) G₁.E G₂.E (glRel_ofT G₁) (glRel_ofT G₂)
  have hterm : ∀ i, ((p : ℚ_[p]) ^ (n.choose 2 * Nat.log p (l + n - 1))) •
      Psi G₁ G₂ S l ((b.coord i).smulRight m) (b i) ∈ M := by
    intro i
    have hφ : (b.coord i).smulRight m ∈ HomLat (K := ℚ_[p]) L M := by
      show ∀ x ∈ L, (b.coord i).smulRight m x ∈ M
      intro x hx
      rw [LinearMap.smulRight_apply]
      exact hZ _ (by rw [Module.Basis.coord_apply]; exact hbi x hx i) m hm
    have hp := weightZeroProj_mem_homLat G₁ G₂ S hLg hMg hφ
    have hI := invariant_integral_holds p (U →ₗ[ℚ_[p]] V) (Fin n) (homAct G₁.E G₂.E) hrel _ hZH hDH l (List.finRange n)
      (List.nodup_finRange n) _ hp
    rw [List.length_finRange] at hI
    have hI' : ∀ x ∈ L, (((p : ℚ_[p]) ^ (n.choose 2 * Nat.log p (l + n - 1))) •
        InvOp (homAct G₁.E G₂.E) l (List.finRange n) (pr0 G₁ G₂ S ((b.coord i).smulRight m))) x ∈ M := hI
    exact hI' (b i) (hbL i)
  rw [QQ_apply, smul_comm, Finset.smul_sum, Nat.cast_smul_eq_nsmul]
  exact AddSubgroup.nsmul_mem _ (AddSubgroup.sum_mem _ fun i _ => hterm i) _
end Formalism.InvariantFactorPaths.PW
