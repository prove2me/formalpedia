-- Prove2me | solution 1 for FixedMachinePrec.serialSchedule_meets_job_count
-- status  : ACCEPTED   (prove)
-- author  : @kj
-- created : 2026-11-26T12:29:40.568725+00:00
-- url     : https://prove2.me/submissions/3d13d518-ef00-4968-b210-9a5840bbc4d4

import Definitions.Def_FixedMachinePrec_Deadline

open FixedMachinePrec

private theorem topo_complete {N : ℕ} (p : Fin N → Fin N → Prop) [DecidableRel p]
    (wf : WellFounded p) :
    let L := topoList p
    L.length = N ∧ (∀ x, x ∈ L) ∧ ∀ x y, p x y → L.idxOf x < L.idxOf y := by
  let Good (l : List (Fin N)) := l.Nodup ∧ ∀ y ∈ l, ∀ x, p x y → x ∈ l ∧ l.idxOf x < l.idxOf y
  let step (l : List (Fin N)) (_ : ℕ) := match (List.finRange N).find? (fun x => decide (x ∉ l ∧ ∀ y, p y x → y ∈ l)) with
    | some x => l ++ [x]
    | none => l
  have finish (xs : List ℕ) (l : List (Fin N)) (hl : Good l) (hn : l.length + xs.length = N) :
      let L := xs.foldl step l
      L.length = N ∧ (∀ x, x ∈ L) ∧ ∀ x y, p x y → L.idxOf x < L.idxOf y := by
    induction xs generalizing l with
    | nil =>
      have hc : l.toFinset = Finset.univ := by
        apply Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
        simp [List.toFinset_card_of_nodup hl.1] at hn ⊢; omega
      have allmem (x : Fin N) : x ∈ l := List.mem_toFinset.mp (hc ▸ Finset.mem_univ x)
      exact ⟨by simpa using hn, allmem,fun x y h => (hl.2 y (allmem y) x h).2⟩
    | cons a xs ih =>
      have missing : ∃ x : Fin N, x ∉ l := by
        by_contra! allmem
        have hc : l.toFinset = Finset.univ := Finset.eq_univ_of_forall (by simpa using allmem)
        have := congrArg Finset.card hc
        simp [List.toFinset_card_of_nodup hl.1] at this
        simp only [List.length_cons] at hn
        omega
      let rem : Set (Fin N) := {x | x ∉ l}
      have hrem : rem.Nonempty := missing
      let z := wf.min rem hrem
      have hz : z ∉ l := wf.min_mem rem hrem
      have hpred (y) (hy : p y z) : y ∈ l := by
        by_contra h
        exact wf.not_lt_min rem (show y ∈ rem from h) hy
      have hit : ((List.finRange N).find? (fun x => decide (x ∉ l ∧ ∀ y, p y x → y ∈ l))).isSome :=
        List.find?_isSome.mpr ⟨z,by simp,decide_eq_true ⟨hz,hpred⟩⟩
      obtain ⟨x,hx⟩ := Option.isSome_iff_exists.mp hit
      have hp : x ∉ l ∧ ∀ y, p y x → y ∈ l := of_decide_eq_true (List.find?_some (p := fun x => decide (x ∉ l ∧ ∀ y, p y x → y ∈ l)) hx)
      have hs : step l a = l ++ [x] := by dsimp only [step]; rw [hx]
      simp only [List.foldl_cons,hs]
      apply ih
      · constructor
        · simp [List.nodup_append, hl.1]; grind
        · intro y hy w hw
          rcases List.mem_append.mp hy with old | new
          · obtain ⟨hmem,hpos⟩ := hl.2 y old w hw
            simp [List.idxOf_append,old,hmem,hpos]
          · have eq : y = x := by simpa using new
            subst y
            have hmem := hp.2 w hw
            simp [List.idxOf_append,hp.1,hmem,List.idxOf_lt_length_of_mem hmem]
      · change (l ++ [x]).length + xs.length = N; simp at hn ⊢; omega
  exact finish (List.range N) [] (by simp [Good]) (by simp)

theorem solution (m : ℕ) (hm : 1 ≤ m) (G : Instance) (hG : G.Acyclic) : (serialSchedule G).MeetsDeadline m G.n := by
  classical
  letI : IsTrans (Fin G.n) G.Prec := ⟨fun _ _ _ => Relation.TransGen.trans⟩
  letI : Std.Irrefl G.Prec := ⟨hG⟩
  obtain ⟨hlen,hmem,hp⟩ := topo_complete G.Prec (Finite.wellFounded_of_trans_of_irrefl G.Prec)
  let idx (x : Fin G.n) := (topoList G.Prec).idxOf x
  have hb (x) : idx x < G.n := hlen ▸ List.idxOf_lt_length_of_mem (hmem x)
  have inj : Function.Injective idx := by
    intro x y e
    have ex := List.getElem_idxOf (List.idxOf_lt_length_of_mem (hmem x))
    have ey := List.getElem_idxOf (List.idxOf_lt_length_of_mem (hmem y))
    change (topoList G.Prec).idxOf x = (topoList G.Prec).idxOf y at e
    simpa [e, ey] using ex.symm
  let σ : Schedule G m := ⟨fun x => idx x, fun _ => ⟨0,hm⟩⟩
  refine ⟨σ,?_,?_,?_⟩
  · intro x; change (idx x : ℝ) = ((idx x+1 : ℕ) : ℝ)-1 ∧ 0=0; simp
  · refine ⟨fun _ => Nat.cast_nonneg _,?_,?_⟩
    · intro x y ne _
      rcases lt_or_gt_of_ne (inj.ne ne) with lt | gt
      · left; change (idx x : ℝ)+1 ≤ idx y; exact_mod_cast lt
      · right; change (idx y : ℝ)+1 ≤ idx x; exact_mod_cast gt
    · intro x y h
      change (idx x : ℝ)+1 ≤ idx y; exact_mod_cast hp x y h
  · unfold Schedule.cmax
    split
    · apply Finset.sup'_le; intro x _; change (idx x : ℝ)+1 ≤ G.n; exact_mod_cast hb x
    · positivity
