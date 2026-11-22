-- Prove2me | solution 1 for CassandrasLafortune.parallel_run_iff
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-22T19:56:14.577406+00:00
-- url     : https://prove2.me/submissions/d8ebe180-4a78-4775-a9ed-33da7df0847e

import Definitions.Def_CassandrasLafortune_Parallel

open CassandrasLafortune RamadgeWonham.Shared

variable {α A B C : Type}

private theorem fold_none (G : Generator α) (w : List α) :
    w.foldl (fun o e ↦ o.bind (G.δ e)) none = none := by
  induction w with
  | nil => rfl
  | cons e w ih => exact ih

/-- Execute the first event, then continue from its successor if it exists. -/
theorem runFrom_cons (G : Generator α) (q : G.Q) (a : α) (w : List α) :
    G.runFrom q (a :: w) = (G.δ a q).bind (fun r ↦ G.runFrom r w) := by
  unfold Generator.runFrom
  simp only [List.foldl_cons, Option.bind_some]
  cases h : G.δ a q with
  | none => exact fold_none G w
  | some r => rfl

private theorem projected_cons {ε : Type} (G : Generator α) (f : ε → Option α)
    (q : G.Q) (e : ε) (w : List ε) :
    G.runFrom q ((e :: w).filterMap f) =
      (localStep G q (f e)).bind (fun r ↦ G.runFrom r (w.filterMap f)) := by
  cases h : f e <;> simp [h, localStep, runFrom_cons]

theorem solution (G : Generator (A ⊕ C)) (H : Generator (B ⊕ C))
    (w : List (Event A B C)) (q : G.Q) (r : H.Q) :
    (parallel G H).run w = some (q, r) ↔
      G.run (w.filterMap Event.left) = some q ∧ H.run (w.filterMap Event.right) = some r := by
  suffices aux : ∀ (p : G.Q) (s : H.Q),
      (parallel G H).runFrom (p, s) w = some (q, r) ↔
        G.runFrom p (w.filterMap Event.left) = some q ∧
        H.runFrom s (w.filterMap Event.right) = some r from aux G.q0 H.q0
  induction w with
  | nil =>
    intro p s
    change some (p, s) = some (q, r) ↔ some p = some q ∧ some s = some r
    simp
  | cons e w ih =>
    intro p s
    rw [runFrom_cons (parallel G H) (p, s) e w, projected_cons G, projected_cons H]
    change ((do
      let p' ← localStep G p e.left
      let s' ← localStep H s e.right
      pure (p', s')) : Option (G.Q × H.Q)).bind _ = _ ↔ _
    cases localStep G p e.left <;> cases localStep H s e.right <;>
      first | exact ih _ _ | simp [Option.bind]
