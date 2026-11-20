-- Prove2me | solution 1 for EnvyFreeCake104.Divide.prefixCut_query_bound__p2m_c286858a_9e65_4696_8505_9d74071d7a32_a1
-- status  : ACCEPTED   (prove)
-- author  : @parclytaxel
-- created : 2026-11-19T09:20:26.762592+00:00
-- url     : https://prove2.me/submissions/8c3a8939-dfdd-40ea-a21e-bcd77491ebe8

import Definitions.Def_EnvyFreeCake104_Divide_Query

open EnvyFreeCake104.Divide

set_option autoImplicit false

theorem run_bind_meter__p2m_7618f8b7_5f76_4ca7_b67c_7ecbc9aa0184_a2
    {ι α β : Type} (V : ι → Valuation) (o : ChoiceOracle ι)
    (m : Prog ι α) (f : α → Prog ι β) (t : List (Event ι)) :
    Prog.run V o (Prog.bind m f) t =
      match Prog.run V o m t with
      | none => none
      | some (a, t') => Prog.run V o (f a) t' := by
  induction m generalizing t with
  | ret a => rfl
  | fail => rfl
  | eval i a b k ih => simpa only [Prog.bind, Prog.run] using ih _ _
  | cut i a b k ih => simpa only [Prog.bind, Prog.run] using ih _ _
  | choose n k ih => simpa only [Prog.bind, Prog.run] using ih _ _

theorem proto_bind_meter__p2m_7618f8b7_5f76_4ca7_b67c_7ecbc9aa0184_a2
    {ι α β : Type} (V : ι → Valuation) (o : ChoiceOracle ι)
    (m : Proto ι α) (f : α → Proto ι β) (A B : ℕ)
    (hm : ∀ s t a s' t', Prog.run V o (m.run s) t = some ((a, s'), t') →
      queryCount t' ≤ queryCount t + A)
    (hf : ∀ a s t b s' t', Prog.run V o ((f a).run s) t = some ((b, s'), t') →
      queryCount t' ≤ queryCount t + B)
    (s : Rec ι) (t : List (Event ι)) (b : β) (s' : Rec ι) (t' : List (Event ι))
    (h : Prog.run V o ((m >>= f).run s) t = some ((b, s'), t')) :
    queryCount t' ≤ queryCount t + (A + B) := by
  change Prog.run V o (Prog.bind (m.run s) (fun r ↦ (f r.1).run r.2)) t =
    some ((b, s'), t') at h
  rw [run_bind_meter__p2m_7618f8b7_5f76_4ca7_b67c_7ecbc9aa0184_a2] at h
  cases he : Prog.run V o (m.run s) t with
  | none => simp [he] at h
  | some r =>
    rcases r with ⟨⟨a, sm⟩, tm⟩
    simp only [he] at h
    have h₁ := hm s t a sm tm he
    have h₂ := hf a sm tm b s' t' h
    omega

theorem proto_pure_meter__p2m_7618f8b7_5f76_4ca7_b67c_7ecbc9aa0184_a2
    {ι α : Type} (V : ι → Valuation) (o : ChoiceOracle ι) (a : α) (B : ℕ)
    (s : Rec ι) (t : List (Event ι)) (x : α) (s' : Rec ι) (t' : List (Event ι))
    (h : Prog.run V o ((pure a : Proto ι α).run s) t = some ((x, s'), t')) :
    queryCount t' ≤ queryCount t + B := by
  change some ((a, s), t) = some ((x, s'), t') at h
  have ht : t = t' := congrArg Prod.snd (Option.some.inj h)
  subst t'
  omega

theorem proto_forIn_meter__p2m_7618f8b7_5f76_4ca7_b67c_7ecbc9aa0184_a2
    {ι α β : Type} (V : ι → Valuation) (o : ChoiceOracle ι)
    (l : List α) (f : α → β → Proto ι (ForInStep β))
    (hf : ∀ a b s t x s' t', Prog.run V o ((f a b).run s) t =
        some ((x, s'), t') → queryCount t' ≤ queryCount t + 1) :
    ∀ b s t x s' t', Prog.run V o ((forIn l b f).run s) t =
      some ((x, s'), t') → queryCount t' ≤ queryCount t + l.length := by
  induction l with
  | nil =>
    intro b s t x s' t' h
    rw [List.forIn_nil] at h
    exact proto_pure_meter__p2m_7618f8b7_5f76_4ca7_b67c_7ecbc9aa0184_a2
      V o b 0 s t x s' t' h
  | cons a l ih =>
    intro b s t x s' t' h
    rw [List.forIn_cons] at h
    have hh : queryCount t' ≤ queryCount t + (1 + l.length) := by
      refine proto_bind_meter__p2m_7618f8b7_5f76_4ca7_b67c_7ecbc9aa0184_a2
        V o _ _ 1 l.length (hf a b) ?_ s t x s' t' h
      intro step sm tm z sz tz hz
      cases step with
      | done v =>
        exact proto_pure_meter__p2m_7618f8b7_5f76_4ca7_b67c_7ecbc9aa0184_a2
          V o v l.length sm tm z sz tz hz
      | yield v => exact ih v sm tm z sz tz hz
    simpa only [List.length_cons, Nat.add_comm 1 l.length] using hh

theorem splitCell_meter__p2m_7618f8b7_5f76_4ca7_b67c_7ecbc9aa0184_a2
    {ι : Type} [DecidableEq ι] (V : ι → Valuation) (o : ChoiceOracle ι)
    (N : Finset ι) (c y : ℝ) (s : Rec ι) (t : List (Event ι))
    (x : Unit) (s' : Rec ι) (t' : List (Event ι))
    (h : Prog.run V o ((splitCell N c y).run s) t = some ((x, s'), t')) :
    queryCount t' ≤ queryCount t + N.card := by
  classical
  unfold splitCell at h
  refine proto_bind_meter__p2m_7618f8b7_5f76_4ca7_b67c_7ecbc9aa0184_a2
    V o _ _ N.card 0 ?_ ?_ s t x s' t' h
  · intro sm tm z sz tz hz
    have hh : queryCount tz ≤ queryCount tm + N.toList.length := by
      refine proto_forIn_meter__p2m_7618f8b7_5f76_4ca7_b67c_7ecbc9aa0184_a2
        V o N.toList _ ?_ _ sm tm z sz tz hz
      intro j b sb tb v sv tv hv
      simp only [StateT.run_bind, evalQ, StateT.run_lift, StateT.run_modify,
        StateT.run_pure, Prog.bind, Prog.run] at hv
      have ht := congrArg Prod.snd (Option.some.inj hv)
      dsimp only at ht
      rw [← ht]
      simp [queryCount, Event.isQuery]
    simpa only [Finset.length_toList] using hh
  · intro u sm tm z sz tz hz
    simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure,
      Prog.bind, Prog.run] at hz
    have ht := congrArg Prod.snd (Option.some.inj hz)
    dsimp only at ht
    rw [← ht]
    omega

theorem proto_cut_meter__p2m_7618f8b7_5f76_4ca7_b67c_7ecbc9aa0184_a2
    {ι : Type} (V : ι → Valuation) (o : ChoiceOracle ι)
    (i : ι) (c w : ℝ) (s : Rec ι) (t : List (Event ι))
    (x : ℝ) (s' : Rec ι) (t' : List (Event ι))
    (h : Prog.run V o ((cutQ i c w).run s) t = some ((x, s'), t')) :
    queryCount t' ≤ queryCount t + 1 := by
  change some ((cutAnswer V i c w, s),
    t ++ [Event.cut i c w (cutAnswer V i c w)]) = some ((x, s'), t') at h
  have ht : t ++ [Event.cut i c w (cutAnswer V i c w)] = t' :=
    congrArg Prod.snd (Option.some.inj h)
  rw [← ht]
  simp [queryCount, Event.isQuery]

theorem solution
    {ι : Type} [DecidableEq ι] (V : ι → Valuation) (N : Finset ι)
    (i : ι) (Q : Piece) (w : ℝ) (s : Rec ι)
    (o : ChoiceOracle ι) (tr₀ : List (Event ι))
    (p : Pos) (s' : Rec ι) (tr : List (Event ι))
    (hrun : Prog.run V o ((prefixCut N i Q w).run s) tr₀ =
      some ((p, s'), tr)) :
    queryCount tr ≤ queryCount tr₀ + (N.card + 1) := by
  classical
  let s₁ : Rec ι := { s with prefixCuts := s.prefixCuts + 1 }
  -- The initial modification and get operation make no oracle calls.
  change Prog.run V o
    ((match findInterval s₁ i Q 0 w with
      | none => if w ≤ 0 then pure (Q.length, 0) else failP
      | some (k, w') =>
        if w' ≤ 0 then pure (k, (Q.getD k default).a)
        else
          match findCell s₁ i
            ((s₁.pts.filter (fun c => (Q.getD k default).a ≤ c ∧
              c < (Q.getD k default).b)).sort (· ≤ ·)) w' with
          | none => failP
          | some (c, w'') => do
            let y ← cutQ i c w''
            if c < y ∧ y < s₁.nextPt c then splitCell N c y
            pure (k, y) : Proto ι Pos).run s₁) tr₀ = some ((p, s'), tr) at hrun
  split at hrun
  · split at hrun
    · exact proto_pure_meter__p2m_7618f8b7_5f76_4ca7_b67c_7ecbc9aa0184_a2
        V o _ (N.card + 1) s₁ tr₀ p s' tr hrun
    · change none = some ((p, s'), tr) at hrun
      contradiction
  · split at hrun
    · exact proto_pure_meter__p2m_7618f8b7_5f76_4ca7_b67c_7ecbc9aa0184_a2
        V o _ (N.card + 1) s₁ tr₀ p s' tr hrun
    · split at hrun
      · change none = some ((p, s'), tr) at hrun
        contradiction
      · have hh : queryCount tr ≤ queryCount tr₀ + (1 + N.card) := by
          refine proto_bind_meter__p2m_7618f8b7_5f76_4ca7_b67c_7ecbc9aa0184_a2
            V o _ _ 1 N.card ?_ ?_ s₁ tr₀ p s' tr hrun
          · intro sm tm z sz tz hz
            exact proto_cut_meter__p2m_7618f8b7_5f76_4ca7_b67c_7ecbc9aa0184_a2
              V o _ _ _ sm tm z sz tz hz
          · intro y sm tm z sz tz hz
            split at hz
            · have hb : queryCount tz ≤ queryCount tm + (N.card + 0) := by
                refine proto_bind_meter__p2m_7618f8b7_5f76_4ca7_b67c_7ecbc9aa0184_a2
                  V o _ _ N.card 0 ?_ ?_ sm tm z sz tz hz
                · intro ss ts u ss' ts' hs
                  exact splitCell_meter__p2m_7618f8b7_5f76_4ca7_b67c_7ecbc9aa0184_a2
                    V o N _ _ ss ts u ss' ts' hs
                · intro u ss ts v ss' ts' hs
                  exact proto_pure_meter__p2m_7618f8b7_5f76_4ca7_b67c_7ecbc9aa0184_a2
                    V o _ 0 ss ts v ss' ts' hs
              simpa only [Nat.add_zero] using hb
            · exact proto_pure_meter__p2m_7618f8b7_5f76_4ca7_b67c_7ecbc9aa0184_a2
                V o _ N.card sm tm z sz tz hz
        omega
