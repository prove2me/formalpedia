-- Prove2me | solution 1 for EnvyFreeCake104.Divide.splitCell_run_explicit__p2m_1bf3b025_64da_41d3_a86c_e0243aee6483_a2
-- status  : ACCEPTED   (prove)
-- author  : @parclytaxel
-- created : 2026-11-19T02:16:35.482202+00:00
-- url     : https://prove2.me/submissions/8c2da420-97f6-497e-8d51-297f4cef5de2

import Definitions.Def_EnvyFreeCake104_Divide_Query

open EnvyFreeCake104.Divide
open scoped Classical

set_option autoImplicit false

-- The continuation form avoids requiring any monad laws for the oracle syntax.
-- As in splitCell itself, equality tests use the scoped classical instance.
theorem splitRows_cont__p2m_7063f87d_5f7a_4f69_9dda_6499da5371ba_a5
    {ι : Type} (V : ι → Valuation) (c y : ℝ)
    (o : ChoiceOracle ι) (k : Proto ι Unit) (L : List ι) (hL : L.Nodup)
    (s : Rec ι) (tr₀ : List (Event ι)) :
    ∃ tr : List (Event ι),
      Prog.run V o ((do
        for j in L do
          let r ← evalQ j c y
          modify fun (t : Rec ι) => { t with
            val := fun i x => if i = j then
              (if x = c then r else if x = y then t.val j c - r else t.val j x)
              else t.val i x }
        k).run s) tr₀ =
      Prog.run V o (k.run ({ s with
        val := fun i x => if i ∈ L then
          (if x = c then evalAnswer V i c y
           else if x = y then s.val i c - evalAnswer V i c y else s.val i x)
          else s.val i x } : Rec ι)) tr := by
  induction L generalizing s tr₀ with
  | nil =>
      exact ⟨tr₀, rfl⟩
  | cons j L ih =>
      obtain ⟨hj, htail⟩ := List.nodup_cons.mp hL
      let sj : Rec ι := { s with
        val := fun i x => if i = j then
          (if x = c then evalAnswer V j c y
           else if x = y then s.val j c - evalAnswer V j c y else s.val j x)
          else s.val i x }
      obtain ⟨tr, htr⟩ := ih htail sj
        (tr₀ ++ [Event.eval j c y (evalAnswer V j c y)])
      refine ⟨tr, ?_⟩
      rw [List.forIn_cons]
      change Prog.run V o ((do
        for a in L do
          let r ← evalQ a c y
          modify fun (t : Rec ι) => { t with
            val := fun i x => if i = a then
              (if x = c then r else if x = y then t.val a c - r else t.val a x)
              else t.val i x }
        k).run sj) (tr₀ ++ [Event.eval j c y (evalAnswer V j c y)]) = _
      rw [htr]
      have hstate : ({ sj with
          val := fun i x => if i ∈ L then
            (if x = c then evalAnswer V i c y
             else if x = y then sj.val i c - evalAnswer V i c y else sj.val i x)
            else sj.val i x } : Rec ι) =
          ({ s with
          val := fun i x => if i ∈ j :: L then
            (if x = c then evalAnswer V i c y
             else if x = y then s.val i c - evalAnswer V i c y else s.val i x)
            else s.val i x } : Rec ι) := by
        apply congrArg (fun v : ι → ℝ → ℝ =>
          ({ pts := s.pts, val := v, prefixCuts := s.prefixCuts } : Rec ι))
        funext i x
        by_cases hi : i = j
        · subst i
          simp [sj, hj]
        · by_cases hm : i ∈ L <;> simp [sj, hi, hm]
      rw [hstate]

theorem solution
    {ι : Type} [DecidableEq ι] (V : ι → Valuation) (N : Finset ι)
    (s : Rec ι) (c y : ℝ) (o : ChoiceOracle ι) (tr₀ : List (Event ι)) :
    ∃ tr : List (Event ι),
      Prog.run V o ((splitCell N c y).run s) tr₀ =
        some (((), ({
             pts := insert y s.pts
             val := fun i x ↦
               if i ∈ N then
                 if x = c then evalAnswer V i c y
                 else if x = y then s.val i c - evalAnswer V i c y
                 else s.val i x
               else s.val i x
             prefixCuts := s.prefixCuts } : Rec ι)), tr) := by
  obtain ⟨tr, htr⟩ :=
    splitRows_cont__p2m_7063f87d_5f7a_4f69_9dda_6499da5371ba_a5
      V c y o (modify fun (t : Rec ι) => { t with pts := insert y t.pts })
      N.toList N.nodup_toList s tr₀
  refine ⟨tr, ?_⟩
  have hfinish (t : Rec ι) (tr' : List (Event ι)) :
      Prog.run V o
        ((modify fun (u : Rec ι) => { u with pts := insert y u.pts } :
          Proto ι Unit).run t) tr' =
        some (((), ({ t with pts := insert y t.pts } : Rec ι)), tr') := by
    rfl
  rw [hfinish] at htr
  simpa only [splitCell, Finset.mem_toList] using htr
