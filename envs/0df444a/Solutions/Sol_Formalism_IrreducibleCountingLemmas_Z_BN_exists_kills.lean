-- Prove2me | solution 1 for Formalism.IrreducibleCountingLemmas.Z.BN.exists_kills
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T10:00:19.597661+00:00
-- url     : https://prove2.me/submissions/38b75653-e5c1-4518-ae6d-39ff490598ff

import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_ZBrauerNesbittAlg
import Definitions.Def_Lemmata_ScalarExtension_Scal
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_ZBrauerNesbitt
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_Z_BN_Kills_mul_right
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_Z_BN_cp_congr
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_Z_BN_exists_ne_zero_hom


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Polynomial
open Formalism Formalism.IrreducibleCountingLemmas Formalism.IrreducibleCountingLemmas.Z Formalism.IrreducibleCountingLemmas.Z.BN
namespace Formalism.IrreducibleCountingLemmas.Z.BN
theorem _root_.solution {K A : Type} [Field K] [Ring A] [Algebra K A]
    (S0 : Type) [AddCommGroup S0] [Module K S0] [Module A S0] [IsScalarTower K A S0]
    [FiniteDimensional K S0] [IsSimpleModule A S0]
    (t : Finset (A → K[X])) (ht : ↑t ⊆ simpleCps K A) (h0 : (cp K S0 : A → K[X]) ∉ t) :
    ∃ a : A, Kills t a ∧ ∃ s : S0, a • s ≠ 0 := by
  classical
  induction t using Finset.induction_on with
  | empty =>
    have := IsSimpleModule.nontrivial A S0
    obtain ⟨s, hs⟩ := exists_ne (0 : S0)
    exact ⟨1, fun F hF => absurd hF (Finset.notMem_empty F), s, by simpa using hs⟩
  | insert F t hFt ih =>
    have ht' : ↑t ⊆ simpleCps K A := fun G hG => ht (by simp [Finset.mem_coe.mp hG])
    have h0' : (cp K S0 : A → K[X]) ∉ t := fun h => h0 (Finset.mem_insert_of_mem h)
    have hne : (cp K S0 : A → K[X]) ≠ F := fun h => h0 (by simp [h])
    obtain ⟨a, ha, s', hs'⟩ := ih ht' h0'
    obtain ⟨S1, i1, i2, i3, i4, i5, i6, hF⟩ := ht (show F ∈ ↑(insert F t) by simp)
    have hx : ∃ x : A, (∀ w : S1, x • w = 0) ∧ ∃ s : S0, x • s ≠ 0 := by
      by_contra hcon
      push Not at hcon
      obtain ⟨f, hf⟩ := exists_ne_zero_hom (k := K) (A := A) (W := S1) (S := S0) hcon
      have e : S1 ≃ₗ[A] S0 := LinearEquiv.ofBijective f (LinearMap.bijective_of_ne_zero hf)
      exact hne (by rw [hF]; funext b; exact (cp_congr e b).symm)
    obtain ⟨x, hx1, s, hs⟩ := hx
    obtain ⟨u, hu⟩ := IsSimpleModule.toSpanSingleton_surjective A hs s'
    refine ⟨a * (u * x), ?_, s, ?_⟩
    · intro G hG
      rcases Finset.mem_insert.mp hG with rfl | hG
      · exact ⟨S1, i1, i2, i3, i4, i5, hF, fun w => by rw [mul_smul, mul_smul, hx1, smul_zero, smul_zero]⟩
      · exact ha.mul_right _ G hG
    · have : u • x • s = s' := by simpa using hu
      rw [mul_smul, mul_smul, this]
      exact hs'
end Formalism.IrreducibleCountingLemmas.Z.BN
