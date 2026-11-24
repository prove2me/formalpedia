-- Prove2me | solution 1 for Formalism.RankSupermodularCovolume.mem_span_inf_of_mem_span
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T11:35:57.483726+00:00
-- url     : https://prove2.me/submissions/6f9c679a-2d9f-43e2-b186-5de04d9a24a5

import Definitions.Def_Formalism_HarderNarasimhan_DegSupermodZ
import Definitions.Def_Formalism_LatticeSlopes_ExistsSaturatedSlopeEqMuMax
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DegSupermodZ
import Theorems.Thm_Formalism_F_saturProps

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Module Submodule
noncomputable section
namespace Formalism.RankSupermodularCovolume
open Formalism.F
section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
private theorem discreteTopology_of_le_discrete (L A : Submodule ℤ E) [DiscreteTopology L] (h : A ≤ L) :
    DiscreteTopology A :=
  DiscreteTopology.of_subset (s := (L : Set E)) ‹_› h
end
end Formalism.RankSupermodularCovolume
namespace Formalism.HN
open Formalism.F Formalism.RankSupermodularCovolume
end Formalism.HN
end
end

set_option autoImplicit false
open Module Submodule
noncomputable section
open Formalism Formalism.RankSupermodularCovolume
open Formalism.F
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
namespace Formalism.RankSupermodularCovolume
theorem _root_.solution (L A B : Submodule ℤ E) [DiscreteTopology L] (hA : A ≤ L)
    (hB : B ≤ L) {b : E} (hbB : b ∈ B) (hbA : b ∈ span ℝ (A : Set E)) :
    b ∈ span ℝ ((A ⊓ B : Submodule ℤ E) : Set E) := by
  classical
  obtain ⟨-, hAAs, hrk⟩ := saturProps E L A ‹_› hA
  haveI : DiscreteTopology (satur L A) := discreteTopology_of_le_discrete L _ inf_le_left
  haveI : DiscreteTopology A := discreteTopology_of_le_discrete L A hA
  have hbAs : b ∈ satur L A := Submodule.mem_inf.2 ⟨hB hbB, hbA⟩
  let N : Submodule ℤ (satur L A) := A.comap (satur L A).subtype
  have hN : Module.finrank ℤ N = Module.finrank ℤ (satur L A) := by
    rw [(Submodule.comapSubtypeEquivOfLe hAAs).finrank_eq]
    exact hrk.symm
  haveI := Submodule.finiteQuotientOfFreeOfRankEq N hN
  have hn : 0 < Nat.card (satur L A ⧸ N) := Nat.card_pos
  have h0 : Nat.card (satur L A ⧸ N) • (Submodule.Quotient.mk ⟨b, hbAs⟩ : satur L A ⧸ N) = 0 :=
    card_nsmul_eq_zero'
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at h0
  have hA' : Nat.card (satur L A ⧸ N) • b ∈ A := by simpa [N] using h0
  have hC : Nat.card (satur L A ⧸ N) • b ∈ A ⊓ B :=
    Submodule.mem_inf.2 ⟨hA', B.nsmul_mem hbB _⟩
  have hb : b = ((Nat.card (satur L A ⧸ N) : ℕ) : ℝ)⁻¹ • (Nat.card (satur L A ⧸ N) • b) := by
    rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul, inv_mul_cancel₀ (by exact_mod_cast hn.ne'), one_smul]
  rw [hb]
  exact Submodule.smul_mem _ _ (Submodule.subset_span hC)
end Formalism.RankSupermodularCovolume
