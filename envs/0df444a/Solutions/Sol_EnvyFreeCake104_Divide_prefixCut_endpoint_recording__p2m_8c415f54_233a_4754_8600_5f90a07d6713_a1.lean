-- Prove2me | solution 1 for EnvyFreeCake104.Divide.prefixCut_endpoint_recording__p2m_8c415f54_233a_4754_8600_5f90a07d6713_a1
-- status  : ACCEPTED   (prove)
-- author  : @parclytaxel
-- created : 2026-11-19T01:50:44.203103+00:00
-- url     : https://prove2.me/submissions/0552ef16-5fa6-444c-8197-48b18020385f

import Definitions.Def_EnvyFreeCake104_Divide_Query

open EnvyFreeCake104.Divide
open scoped Classical

set_option autoImplicit false

private theorem fi_update__p2m_9b8f1de4_1ca8_4e82_a2d5_046493ddc8fb_a2 {ι : Type} (s : Rec ι)
    (i : ι) (n : ℕ) (Q : Piece) (k : ℕ) (w : ℝ) :
    findInterval {s with prefixCuts := n} i Q k w = findInterval s i Q k w := by
  induction Q generalizing k w with
  | nil => rfl
  | cons I Q ih =>
    change (if w ≤ s.intervalVal i I then some (k, w) else
      findInterval {s with prefixCuts := n} i Q (k + 1) (w - s.intervalVal i I)) = _
    rw [ih]
    rfl

private theorem fc_update__p2m_9b8f1de4_1ca8_4e82_a2d5_046493ddc8fb_a2 {ι : Type} (s : Rec ι)
    (i : ι) (n : ℕ) (cs : List ℝ) (w : ℝ) :
    findCell {s with prefixCuts := n} i cs w = findCell s i cs w := by
  induction cs generalizing w with
  | nil => rfl
  | cons c cs ih =>
    change (if w ≤ s.val i c then some (c, w) else
      findCell {s with prefixCuts := n} i cs (w - s.val i c)) = _
    rw [ih]
    rfl

private theorem fi_member__p2m_9b8f1de4_1ca8_4e82_a2d5_046493ddc8fb_a2 {ι : Type} (s : Rec ι)
    (i : ι) (Q : Piece) (n : ℕ) (w : ℝ) (k : ℕ) (r : ℝ)
    (h : findInterval s i Q n w = some (k, r)) :
    n ≤ k ∧ k < n + Q.length ∧ (Q.getD (k - n) default) ∈ Q := by
  induction Q generalizing n w with
  | nil => simp [findInterval] at h
  | cons I Q ih =>
    simp only [findInterval] at h
    split at h
    · have hk : n = k := congrArg Prod.fst (Option.some.inj h)
      subst k
      exact ⟨le_rfl, by simp only [List.length_cons]; omega, by simp⟩
    · obtain ⟨hlo, hhi, hmem⟩ := ih (n + 1) (w - s.intervalVal i I) h
      refine ⟨by omega, by simp only [List.length_cons]; omega, ?_⟩
      have hk : k - n = (k - (n + 1)) + 1 := by omega
      rw [hk, List.getD_cons_succ]
      exact List.mem_cons_of_mem I hmem

private theorem run_bind__p2m_9b8f1de4_1ca8_4e82_a2d5_046493ddc8fb_a2 {ι α β : Type}
    (V : ι → Valuation) (o : ChoiceOracle ι) (m : Prog ι α)
    (f : α → Prog ι β) (tr : List (Event ι)) :
    Prog.run V o (Prog.bind m f) tr =
      (match Prog.run V o m tr with
      | none => none
      | some (a, tr') => Prog.run V o (f a) tr') := by
  induction m generalizing tr with
  | ret a => rfl
  | fail => rfl
  | eval j a b cont ih => exact ih _ _
  | cut j a b cont ih => exact ih _ _
  | choose n cont ih => exact ih _ _

theorem solution
    {ι : Type} [DecidableEq ι] (V : ι → Valuation) (N : Finset ι)
    (hsplit : ∀ (t : Rec ι), t.Valid V N →
      ∀ (c y : ℝ), c ∈ t.pts → c < y → y < t.nextPt c →
      ∀ (o : ChoiceOracle ι) (tr₀ : List (Event ι)),
      ∃ (t' : Rec ι) (tr : List (Event ι)),
        Prog.run V o ((splitCell N c y).run t) tr₀ = some (((), t'), tr) ∧
        t'.Valid V N ∧ t'.pts = insert y t.pts)
    (i : ι) (Q : Piece) (s : Rec ι) (hs : s.Valid V N)
    (hstarts : ∀ I ∈ Q, I.a ∈ s.pts)
    (hsafe : ∀ I ∈ Q, ∀ (r : ℝ), 0 < r → ∀ (c t : ℝ),
      findCell s i
        ((s.pts.filter (fun c => I.a ≤ c ∧ c < I.b)).sort (· ≤ ·)) r =
          some (c, t) →
      c ∈ s.pts ∧
        (cutAnswer V i c t ∈ s.pts ∨
          (c < cutAnswer V i c t ∧ cutAnswer V i c t < s.nextPt c)))
    (w : ℝ) (p : Pos)
    (hp : (match findInterval s i Q 0 w with
        | none => if w ≤ 0 then some (Q.length, (0 : ℝ)) else none
        | some (k, r) =>
          if r ≤ 0 then some (k, (Q.getD k default).a)
          else
            match findCell s i
                ((s.pts.filter (fun c => (Q.getD k default).a ≤ c ∧
                  c < (Q.getD k default).b)).sort (· ≤ ·)) r with
            | none => none
            | some (c, t) => some (k, cutAnswer V i c t)) = some p)
    (o : ChoiceOracle ι) (tr₀ : List (Event ι)) :
    ∃ (s' : Rec ι) (tr : List (Event ι)),
      Prog.run V o ((prefixCut N i Q w).run s) tr₀ = some ((p, s'), tr) ∧
      s'.Valid V N ∧ s.pts ⊆ s'.pts ∧
      (p.1 < Q.length → p.2 ∈ s'.pts) := by
  classical
  let s₀ : Rec ι := {s with prefixCuts := s.prefixCuts + 1}
  have hs₀ : s₀.Valid V N := hs
  have hexpand : (prefixCut N i Q w).run s =
      ((match findInterval s i Q 0 w with
      | none => if w ≤ 0 then pure (Q.length, (0 : ℝ)) else failP
      | some (k, r) =>
        if r ≤ 0 then pure (k, (Q.getD k default).a)
        else match findCell s i
            ((s.pts.filter (fun c => (Q.getD k default).a ≤ c ∧
              c < (Q.getD k default).b)).sort (· ≤ ·)) r with
          | none => failP
          | some (c, t) => do
              let y ← cutQ i c t
              if c < y ∧ y < s.nextPt c then splitCell N c y
              return (k, y) : Proto ι Pos).run s₀) := by
    let F (z : Rec ι) : Proto ι Pos :=
      match findInterval z i Q 0 w with
      | none => if w ≤ 0 then pure (Q.length, (0 : ℝ)) else failP
      | some (k, r) =>
        if r ≤ 0 then pure (k, (Q.getD k default).a)
        else match findCell z i
            ((z.pts.filter (fun c => (Q.getD k default).a ≤ c ∧
              c < (Q.getD k default).b)).sort (· ≤ ·)) r with
          | none => failP
          | some (c, t) => do
              let y ← cutQ i c t
              if c < y ∧ y < s.nextPt c then splitCell N c y
              return (k, y)
    change (F s₀).run s₀ = (F s).run s₀
    have hF : F s₀ = F s := by
      dsimp only [F]
      simp only [s₀, fi_update__p2m_9b8f1de4_1ca8_4e82_a2d5_046493ddc8fb_a2,
        fc_update__p2m_9b8f1de4_1ca8_4e82_a2d5_046493ddc8fb_a2]
    exact congrArg (fun m : Proto ι Pos => m.run s₀) hF
  rw [hexpand]
  cases hfi : findInterval s i Q 0 w with
  | none =>
    simp only [hfi] at hp ⊢
    by_cases hw : w ≤ 0
    · rw [if_pos hw] at hp ⊢
      cases Option.some.inj hp
      refine ⟨s₀, tr₀, rfl, hs₀, ?_, ?_⟩
      · exact fun _ h => h
      · intro h
        exact (Nat.lt_irrefl Q.length h).elim
    · simp [hw] at hp
  | some kr =>
    rcases kr with ⟨k, r⟩
    simp only [hfi] at hp ⊢
    have hI : Q.getD k default ∈ Q := by
      simpa using (fi_member__p2m_9b8f1de4_1ca8_4e82_a2d5_046493ddc8fb_a2 s i Q 0 w k r hfi).2.2
    by_cases hr : r ≤ 0
    · rw [if_pos hr] at hp ⊢
      cases Option.some.inj hp
      exact ⟨s₀, tr₀, rfl, hs₀, (fun _ h => h), (fun _ => hstarts _ hI)⟩
    · rw [if_neg hr] at hp ⊢
      cases hfc : findCell s i
          ((s.pts.filter (fun c => (Q.getD k default).a ≤ c ∧
            c < (Q.getD k default).b)).sort (· ≤ ·)) r with
      | none =>
        rw [hfc] at hp
        cases hp
      | some ct =>
        rcases ct with ⟨c, t⟩
        simp only [hfc] at hp ⊢
        cases Option.some.inj hp
        obtain ⟨hc, hy⟩ := hsafe _ hI r (lt_of_not_ge hr) c t hfc
        let y : ℝ := cutAnswer V i c t
        let tr₁ : List (Event ι) := tr₀ ++ [Event.cut i c t y]
        by_cases hinter : c < y ∧ y < s.nextPt c
        · obtain ⟨s', tr, hrun, hvalid, hpts⟩ :=
            hsplit s₀ hs₀ c y hc hinter.1 hinter.2 o tr₁
          refine ⟨s', tr, ?_, hvalid, ?_, ?_⟩
          · change Prog.run V o
                ((do
                  if c < y ∧ y < s.nextPt c then splitCell N c y
                  return (k, y) : Proto ι Pos).run s₀) tr₁ = _
            simp only [if_pos hinter]
            change Prog.run V o
                (Prog.bind ((splitCell N c y).run s₀)
                  (fun us => Prog.ret ((k, y), us.2))) tr₁ = _
            rw [run_bind__p2m_9b8f1de4_1ca8_4e82_a2d5_046493ddc8fb_a2, hrun]
            rfl
          · intro x hx
            rw [hpts]
            exact Finset.mem_insert_of_mem hx
          · intro _
            rw [hpts]
            exact Finset.mem_insert_self _ _
        · have hypts : y ∈ s.pts := hy.resolve_right hinter
          refine ⟨s₀, tr₁, ?_, hs₀, (fun _ h => h), (fun _ => hypts)⟩
          change Prog.run V o
              ((do
                if c < y ∧ y < s.nextPt c then splitCell N c y
                return (k, y) : Proto ι Pos).run s₀) tr₁ = _
          simp only [if_neg hinter]
          rfl
