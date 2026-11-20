-- Prove2me | solution 1 for EnvyFreeCake104.Divide.exec_bind_transfer__p2m_7c833f14_cb58_4a57_947b_39a2d0559683_a1
-- status  : ACCEPTED   (prove)
-- author  : @parclytaxel
-- created : 2026-11-19T15:08:44.524968+00:00
-- url     : https://prove2.me/submissions/f8dc1dd7-2876-4ca5-8308-b4a2aef69cc7

import Definitions.Def_EnvyFreeCake104_Divide_Query

open EnvyFreeCake104.Divide

set_option autoImplicit false

theorem run_bind__p2m_58b54c2a_60fe_4158_b73e_8c0bf7b0cdaf_a2
    {ι α β : Type} (V : ι → Valuation) (o : ChoiceOracle ι)
    (p : Prog ι α) (f : α → Prog ι β) (tr : List (Event ι)) :
    Prog.run V o (Prog.bind p f) tr =
      match Prog.run V o p tr with
      | none => none
      | some (x, tr') => Prog.run V o (f x) tr' := by
  induction p generalizing tr with
  | ret x => rfl
  | fail => rfl
  | eval i a b k ih =>
      simp only [Prog.bind, Prog.run]
      exact ih (evalAnswer V i a b) (tr ++ [Event.eval i a b (evalAnswer V i a b)])
  | cut i x w k ih =>
      simp only [Prog.bind, Prog.run]
      exact ih (cutAnswer V i x w) (tr ++ [Event.cut i x w (cutAnswer V i x w)])
  | choose m k ih =>
      simp only [Prog.bind, Prog.run]
      exact ih (o tr m) (tr ++ [Event.choice m (o tr m)])

theorem run_shift__p2m_58b54c2a_60fe_4158_b73e_8c0bf7b0cdaf_a2
    {ι α : Type} (V : ι → Valuation) (o : ChoiceOracle ι)
    (p : Prog ι α) (pretr tr : List (Event ι)) :
    Prog.run V o p (pretr ++ tr) =
      (Prog.run V (fun t m ↦ o (pretr ++ t) m) p tr).map
        (fun r : α × List (Event ι) ↦ (r.1, pretr ++ r.2)) := by
  induction p generalizing tr with
  | ret x => rfl
  | fail => rfl
  | eval i a b k ih =>
      simpa only [Prog.run, List.append_assoc] using
        ih (evalAnswer V i a b) (tr ++ [Event.eval i a b (evalAnswer V i a b)])
  | cut i x w k ih =>
      simpa only [Prog.run, List.append_assoc] using
        ih (cutAnswer V i x w) (tr ++ [Event.cut i x w (cutAnswer V i x w)])
  | choose m k ih =>
      simpa only [Prog.run, List.append_assoc] using
        ih (o (pretr ++ tr) m) (tr ++ [Event.choice m (o (pretr ++ tr) m)])

theorem exec_run_iff__p2m_58b54c2a_60fe_4158_b73e_8c0bf7b0cdaf_a2
    {ι α : Type} (V : ι → Valuation) (o : ChoiceOracle ι)
    (p : Proto ι α) (s : Rec ι) (x : α) (s' : Rec ι) (tr : List (Event ι)) :
    exec V o p s = some (x, s', tr) ↔
      Prog.run V o (p.run s) [] = some ((x, s'), tr) := by
  unfold exec
  cases Prog.run V o (p.run s) [] with
  | none => simp
  | some r =>
      rcases r with ⟨⟨u, t⟩, l⟩
      simp only [Option.some.injEq, Prod.mk.injEq, and_assoc]

theorem solution
    {ι α β : Type} (V : ι → Valuation) (o : ChoiceOracle ι)
    (a : Proto ι α) (b : α → Proto ι β) (s : Rec ι)
    (x : α) (s₁ : Rec ι) (tr₁ : List (Event ι))
    (ha : exec V o a s = some (x, s₁, tr₁)) :
    ∃ o₁ : ChoiceOracle ι, ∀ (y : β) (s₂ : Rec ι) (tr₂ : List (Event ι)),
      exec V o₁ (b x) s₁ = some (y, s₂, tr₂) →
      ∃ tr : List (Event ι),
        exec V o (do let z ← a; b z) s = some (y, s₂, tr) ∧
        queryCount tr = queryCount tr₁ + queryCount tr₂ := by
  let o₁ : ChoiceOracle ι := fun t m ↦ o (tr₁ ++ t) m
  refine ⟨o₁, ?_⟩
  intro y s₂ tr₂ hb
  have ha' :=
    (exec_run_iff__p2m_58b54c2a_60fe_4158_b73e_8c0bf7b0cdaf_a2
      V o a s x s₁ tr₁).mp ha
  have hb' :=
    (exec_run_iff__p2m_58b54c2a_60fe_4158_b73e_8c0bf7b0cdaf_a2
      V o₁ (b x) s₁ y s₂ tr₂).mp hb
  dsimp only [o₁] at hb'
  have hs : Prog.run V o ((b x).run s₁) tr₁ =
      some ((y, s₂), tr₁ ++ tr₂) := by
    simpa only [List.append_nil, hb', Option.map_some] using
      run_shift__p2m_58b54c2a_60fe_4158_b73e_8c0bf7b0cdaf_a2
        V o ((b x).run s₁) tr₁ []
  refine ⟨tr₁ ++ tr₂, ?_, ?_⟩
  · apply (exec_run_iff__p2m_58b54c2a_60fe_4158_b73e_8c0bf7b0cdaf_a2
      V o (do let z ← a; b z) s y s₂ (tr₁ ++ tr₂)).mpr
    change Prog.run V o
      (Prog.bind (a.run s) (fun (z, t) ↦ (b z).run t)) [] = _
    rw [run_bind__p2m_58b54c2a_60fe_4158_b73e_8c0bf7b0cdaf_a2, ha']
    exact hs
  · exact List.countP_append
