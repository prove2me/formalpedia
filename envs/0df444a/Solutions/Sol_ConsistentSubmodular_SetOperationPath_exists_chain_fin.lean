-- Prove2me | solution 1 for ConsistentSubmodular.SetOperationPath.exists_chain_fin
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-13T16:35:21.246201+00:00
-- url     : https://prove2.me/submissions/002b3445-6c9b-4d50-b64b-402bd917f0fc

import Mathlib
import Definitions.Def_ConsistentSubmodular_Deterministic_Reduction_OperationPath
import Theorems.Thm_ConsistentSubmodular_SetOperationPath_exists_chain

section

open scoped BigOperators
open ConsistentSubmodular
open ConsistentSubmodular.SetOperationPath
variable {n : ℕ}

theorem solution {K : ℕ} (S : Fin (K + 1) → Finset (Fin n))
    (B : ℕ) (U : Finset (Fin n)) (good : Finset (Fin n) → Prop)
    (hmono : ∀ A B, A ⊆ B → good A → good B)
    (hstart : good (S 0))
    (hnodes : ∀ i, S i ⊆ U ∧ (S i).card ≤ B)
    (hinter : ∀ i : Fin K, good (S i.castSucc ∩ S i.succ)) :
    ∃ P : SetOperationPath n,
      P.length = ∑ i : Fin K, recourse (S i.castSucc) (S i.succ) ∧
      P.node 0 = S 0 ∧ P.node P.length = S (Fin.last K) ∧
      ∀ i, P.node i ⊆ U ∧ (P.node i).card ≤ B ∧ good (P.node i) := by
  let s : ℕ → Finset (Fin n) := fun i => S ⟨min i K, by omega⟩
  have hi (i : ℕ) (hi : i ≤ K) : s i = S ⟨i, by omega⟩ := by simp [s, Nat.min_eq_left hi]
  obtain ⟨P, hlen, hinit, hterm, hP⟩ := exists_chain s K B U good hmono
    (by simpa [s] using hstart)
    (fun i hi' => by rw [hi i hi']; exact hnodes _)
    (fun i hi' => by
      rw [hi i (by omega), hi (i + 1) (by omega)]
      exact hinter ⟨i, hi'⟩)
  refine ⟨P, ?_, ?_, ?_, hP⟩
  · rw [hlen]
    rw [← Fin.sum_univ_eq_sum_range]
    apply Finset.sum_congr rfl
    intro i _
    rw [hi i.val (by omega), hi (i.val + 1) (by omega)]
    rfl
  · simpa [s] using hinit
  · simpa [s, Fin.last] using hterm

end
