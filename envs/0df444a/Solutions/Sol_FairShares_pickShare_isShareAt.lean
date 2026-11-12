-- Prove2me | solution 1 for FairShares.pickShare_isShareAt
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-11T20:00:27.616198+00:00
-- url     : https://prove2.me/submissions/a6a44739-1c2e-433d-87ab-62fd6146da3e

import Definitions.Def_FairShares_pickShare
import Definitions.Def_FairShares_IsShareAt

namespace Aux_FairShares_pickShare_isShareAt
open FairShares

private lemma gameVal_exists_bundle {m n : ℕ} (v : Finset (Fin m) → ℝ) (k : Fin n) :
    ∀ (ps : List (Fin n)) (R H : Finset (Fin m)),
      ∃ S : Finset (Fin m), gameVal v k ps R H = v S
  | [], _, H => ⟨H, rfl⟩
  | p :: ps, R, H => by
    unfold gameVal
    split_ifs with hR hpk
    · rcases Finset.exists_mem_eq_sup' hR
        (fun e => gameVal v k ps (R.erase e) (insert e H)) with ⟨e, _, he⟩
      rcases gameVal_exists_bundle v k ps (R.erase e) (insert e H) with ⟨S, hS⟩
      exact ⟨S, he.trans hS⟩
    · rcases Finset.exists_mem_eq_inf' hR
        (fun e => gameVal v k ps (R.erase e) H) with ⟨e, _, he⟩
      rcases gameVal_exists_bundle v k ps (R.erase e) H with ⟨S, hS⟩
      exact ⟨S, he.trans hS⟩
    · exact ⟨H, rfl⟩

private lemma sup'_map_eq {α β : Type*} (s : Finset α) (hs : s.Nonempty) (f : α ↪ β) (g : β → ℝ) :
    (s.map f).sup' (Finset.map_nonempty.mpr hs) g = s.sup' hs (fun x => g (f x)) := by
  refine le_antisymm (Finset.sup'_le _ _ fun y hy => ?_) (Finset.sup'_le _ _ fun x hx => ?_)
  · rcases Finset.mem_map.mp hy with ⟨x, hx, rfl⟩
    exact Finset.le_sup' (fun z => g (f z)) hx
  · exact Finset.le_sup' g (Finset.mem_map_of_mem f hx)

private lemma inf'_map_eq {α β : Type*} (s : Finset α) (hs : s.Nonempty) (f : α ↪ β) (g : β → ℝ) :
    (s.map f).inf' (Finset.map_nonempty.mpr hs) g = s.inf' hs (fun x => g (f x)) := by
  refine le_antisymm (Finset.le_inf' _ _ fun x hx => ?_) (Finset.le_inf' _ _ fun y hy => ?_)
  · exact Finset.inf'_le g (Finset.mem_map_of_mem f hx)
  · rcases Finset.mem_map.mp hy with ⟨x, hx, rfl⟩
    exact Finset.inf'_le (fun z => g (f z)) hx

private lemma map_erase_eq {α β : Type*} [DecidableEq α] [DecidableEq β]
    (s : Finset α) (f : α ↪ β) (a : α) :
    (s.erase a).map f = (s.map f).erase (f a) := by
  ext y
  simp only [Finset.mem_map, Finset.mem_erase]
  constructor
  · rintro ⟨x, ⟨hne, hx⟩, rfl⟩
    exact ⟨f.injective.ne hne, x, hx, rfl⟩
  · rintro ⟨hne, x, hx, rfl⟩
    exact ⟨x, ⟨fun h => hne (congrArg f h), hx⟩, rfl⟩

private lemma gameVal_rename {m n : ℕ} (σ : Equiv.Perm (Fin m))
    (v : Finset (Fin m) → ℝ) (k : Fin n) :
    ∀ (ps : List (Fin n)) (R H : Finset (Fin m)),
      gameVal (fun S => v (S.map σ.toEmbedding)) k ps R H =
        gameVal v k ps (R.map σ.toEmbedding) (H.map σ.toEmbedding)
  | [], _, H => rfl
  | p :: ps, R, H => by
    unfold gameVal
    by_cases hR : R.Nonempty
    · have hRm : (R.map σ.toEmbedding).Nonempty := Finset.map_nonempty.mpr hR
      simp only [hR, hRm, ↓reduceDIte]
      split_ifs with hpk
      · rw [sup'_map_eq R hR σ.toEmbedding]
        refine Finset.sup'_congr hR rfl fun e _ => ?_
        rw [gameVal_rename σ v k ps (R.erase e) (insert e H), map_erase_eq, Finset.map_insert]
      · rw [inf'_map_eq R hR σ.toEmbedding]
        refine Finset.inf'_congr hR rfl fun e _ => ?_
        rw [gameVal_rename σ v k ps (R.erase e) H, map_erase_eq]
    · have hRm : ¬ (R.map σ.toEmbedding).Nonempty := by simpa using hR
      simp [hR, hRm]

end Aux_FairShares_pickShare_isShareAt

open FairShares Aux_FairShares_pickShare_isShareAt

theorem solution {m n : ℕ} (hn : 1 ≤ n) (ω : Fin m → Fin n)
    (D : Set (Finset (Fin m) → ℝ)) :
    IsShareAt D (pickShare ω) := by
  refine ⟨fun v _ => ?_, fun σ v _ _ => ?_⟩
  · let k₀ : Fin n := ⟨0, hn⟩
    rcases gameVal_exists_bundle v k₀ (List.ofFn ω) Finset.univ ∅ with ⟨S, hS⟩
    refine ⟨S, ?_⟩
    unfold pickShare pickValue
    exact (ciInf_le (Finite.bddBelow_range _) k₀).trans hS.le
  · unfold pickShare pickValue
    congr 1
    ext k
    rw [gameVal_rename σ v k (List.ofFn ω) Finset.univ ∅]
    have huniv : (Finset.univ : Finset (Fin m)).map σ.toEmbedding = Finset.univ := by
      ext x
      simp only [Finset.mem_map, Finset.mem_univ, Equiv.toEmbedding_apply, true_and, iff_true]
      exact ⟨σ.symm x, σ.apply_symm_apply x⟩
    rw [huniv, Finset.map_empty]
