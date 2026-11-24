-- Prove2me | solution 1 for Formalism.GM.badCrit_core
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:34:10.229631+00:00
-- url     : https://prove2.me/submissions/e8c6cd1f-8849-42b9-bf57-cbd98e82b041

import Definitions.Def_Formalism_MahlerMeasure_StatementT
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_BadCrit
import Theorems.Thm_Formalism_GM_badCrit_dvd_pow_of_norm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM
open Module
namespace Formalism.GM
theorem _root_.solution {p : ℕ} [Fact p.Prime] {m : ℕ} (E : ℕ) (N : Submodule ℤ_[p] (Fin m → ℤ_[p]))
    (h : ∀ l : (Fin m → ℤ_[p]) →ₗ[ℤ_[p]] ℤ_[p], (∃ z, l z = 1) →
      ∃ v ∈ N, (p : ℝ) ^ (-(E : ℤ)) ≤ ‖l v‖) :
    ∀ z, (p : ℤ_[p]) ^ E • z ∈ N := by
  classical
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  obtain ⟨n, S⟩ := N.smithNormalForm (Pi.basisFun ℤ_[p] (Fin m))
  have hr : ∀ j, j ∈ Set.range S.f := by
    intro j
    by_contra hj
    obtain ⟨v, hv, hn⟩ := h (S.bM.coord j) ⟨S.bM j, by simp⟩
    have h0 : S.bM.coord j v = 0 := S.le_ker_coord_of_notMem_range hj hv
    rw [h0, norm_zero] at hn
    exact absurd hn (not_le.2 (zpow_pos hp0 _))
  have hd : ∀ i, S.a i ∣ (p : ℤ_[p]) ^ E := by
    intro i
    obtain ⟨v, hv, hn⟩ := h (S.bM.coord (S.f i)) ⟨S.bM (S.f i), by simp⟩
    have hc : S.bM.coord (S.f i) v = S.a i * S.bN.coord i ⟨v, hv⟩ := by
      show S.bM.repr ((⟨v, hv⟩ : N) : Fin m → ℤ_[p]) (S.f i) = S.a i * S.bN.repr ⟨v, hv⟩ i
      rw [S.repr_apply_embedding_eq_repr_smul]
      exact congrArg (· i) (S.bN.repr.map_smul (S.a i) ⟨v, hv⟩)
    apply badCrit_dvd_pow_of_norm
    calc _ ≤ _ := hn
      _ = ‖S.a i‖ * ‖S.bN.coord i ⟨v, hv⟩‖ := by rw [hc, norm_mul]
      _ ≤ ‖S.a i‖ * 1 := by gcongr; exact PadicInt.norm_le_one _
      _ = _ := mul_one _
  have hb : ∀ j, (p : ℤ_[p]) ^ E • S.bM j ∈ N := by
    intro j
    obtain ⟨i, rfl⟩ := hr j
    obtain ⟨t, ht⟩ := hd i
    rw [ht, mul_comm, mul_smul, ← S.snf i]
    exact N.smul_mem t (S.bN i).2
  intro z
  rw [← S.bM.sum_repr z, Finset.smul_sum]
  refine N.sum_mem fun j _ => ?_
  rw [smul_comm]
  exact N.smul_mem _ (hb j)
end Formalism.GM
