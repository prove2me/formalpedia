-- Prove2me | solution 1 for DirectedHamiltonicity.Main.proposition3
-- status  : ACCEPTED   (prove)
-- author  : @Soh Kumabe
-- created : 2026-11-26T06:52:29.613117+00:00
-- url     : https://prove2.me/submissions/f57eb83a-6125-45b6-a130-fa0491b56d77

import Theorems.Thm_DirectedHamiltonicity_Main_lemma5

open DirectedHamiltonicity.Main DirectedHamiltonicity.Main.Multidigraph MvPolynomial Classical

namespace DHCSelections

variable {V : Type} [Fintype V] [DecidableEq V] (adj : V → V → Prop) [DecidableRel adj]
variable (s t : V) (hs : ∀ u, ¬ adj u s) {d : ℕ}
private abbrev Vertex (s : V) := {v : V // v ≠ s}
private abbrev Pos := Fin (Fintype.card V - 1)
private def dest (a : SArc adj) : Vertex s :=
  ⟨a.1.2, fun h => hs a.1.1 (h ▸ a.2)⟩

/-- The heads along a Hamiltonian path enumerate the non-start vertices. -/
private noncomputable def headEquiv (P : Pos (V := V) → SArc adj)
    (hP : P ∈ (ofAdj adj).hamPaths s t) : Pos (V := V) ≃ Vertex s := by
  classical
  apply Equiv.ofBijective (fun j => dest adj s hs (P j))
  apply (Fintype.bijective_iff_injective_and_card _).2
  constructor
  · intro i j hij
    have h := (Finset.mem_filter.mp hP).2.2.1
    apply Fin.succ_injective
    apply h
    simpa [walkVerts, ofAdj, dest] using congrArg Subtype.val hij
  · simp [Pos, Vertex, Fintype.card_subtype_compl]

private def Fits (S : SArc adj → Finset (Fin d)) (sel : Vertex s → Fin d)
    (P : Pos (V := V) → SArc adj) := ∀ j, sel (dest adj s hs (P j)) ∈ S (P j)

private noncomputable def mon (sel : Vertex s → Fin d) :
    MvPolynomial (Vertex s × Fin d) (ZMod 2) := ∏ v, X (v,sel v)

private theorem expand_path (S : SArc adj → Finset (Fin d))
    (P : Pos (V := V) → SArc adj) (hP : P ∈ (ofAdj adj).hamPaths s t) :
    (∏ j, ∑ l ∈ S (P j), (X (dest adj s hs (P j),l) : MvPolynomial _ (ZMod 2))) =
      ∑ sel, if Fits adj s hs S sel P then mon s sel else 0 := by
  classical
  let e := headEquiv adj s t hs P hP
  have split (j : Pos (V := V)) :
      (∑ l ∈ S (P j), (X (e j,l) : MvPolynomial _ (ZMod 2))) =
        ∑ l : Fin d, if l ∈ S (P j) then X (e j,l) else 0 := by
    simp
  change (∏ j, ∑ l ∈ S (P j), (X (e j,l) : MvPolynomial _ (ZMod 2))) = _
  simp_rw [split]
  rw [Fintype.prod_sum]
  let reindex := Equiv.arrowCongr e (Equiv.refl (Fin d))
  apply Fintype.sum_equiv reindex
  intro labs
  rw [Fintype.prod_ite_zero]
  have he (j) : reindex labs (e j) = labs j := by simp [reindex, Equiv.arrowCongr]
  have heq : Fits adj s hs S (reindex labs) P ↔ ∀ j, labs j ∈ S (P j) := by
    change (∀ j, reindex labs (e j) ∈ _) ↔ _
    simp_rw [he]
  rw [heq]
  split_ifs
  · apply Fintype.prod_equiv e
    intro j
    rw [he]
  · rfl

omit [DecidableEq V] in
private theorem selected_count (S : SArc adj → Finset (Fin d)) (sel : Vertex s → Fin d) :
    ((selectedGraph adj S s sel).hamPaths s t).card =
      (((ofAdj adj).hamPaths s t).filter (Fits adj s hs S sel)).card := by
  classical
  let proj := fun e : {c // InSelectedGroup adj S s sel c} => e.1.1
  have fits_edge (e : {c // InSelectedGroup adj S s sel c}) :
      sel (dest adj s hs (proj e)) ∈ S (proj e) := by
    obtain ⟨h,hl⟩ := e.2
    exact hl ▸ e.1.2.2
  have inj : Function.Injective proj := by
    rintro ⟨⟨a,la⟩,ha⟩ ⟨⟨b,lb⟩,hb⟩ h
    change a = b at h
    subst b
    obtain ⟨_,hla⟩ := ha
    obtain ⟨_,hlb⟩ := hb
    have hl : la = lb := Subtype.ext (hla.trans hlb.symm)
    subst lb
    rfl
  have path (Q : Pos (V := V) → {c // InSelectedGroup adj S s sel c}) :
      Q ∈ (selectedGraph adj S s sel).hamPaths s t ↔
        (fun i => proj (Q i)) ∈ (ofAdj adj).hamPaths s t := by
    simp only [hamPaths, Finset.mem_filter, Finset.mem_univ, true_and]
    rfl
  apply Finset.card_bij (fun Q _ i => proj (Q i))
  · intro Q hQ; exact Finset.mem_filter.mpr ⟨(path Q).1 hQ, fun i => fits_edge (Q i)⟩
  · intro Q _ Q' _ he; exact funext fun i => inj (congrFun he i)
  · intro P hP
    obtain ⟨hp,hf⟩ := Finset.mem_filter.mp hP
    let Q : Pos (V := V) → {c // InSelectedGroup adj S s sel c} := fun i =>
      ⟨⟨P i, sel (dest adj s hs (P i)), hf i⟩, (dest adj s hs (P i)).2, rfl⟩
    exact ⟨Q, (path Q).2 hp,rfl⟩

include hs in
private theorem good_of_nonzero (S : SArc adj → Finset (Fin d))
    (hn : pathPoly adj s t S ≠ 0) :
    ∃ sel : Vertex s → Fin d, Odd ((selectedGraph adj S s sel).hamPaths s t).card := by
  classical
  by_contra! h
  apply hn
  let paths := (ofAdj adj).hamPaths s t
  have expand : pathPoly adj s t S = ∑ P ∈ paths, ∑ sel,
      if Fits adj s hs S sel P then mon s sel else 0 := by
    unfold pathPoly
    apply Finset.sum_congr rfl
    intro P hP
    convert! expand_path adj s t hs S P hP using 1
    apply Finset.prod_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro l _
    have hi : (P i).1.2 ≠ s := (dest adj s hs (P i)).2
    simp [hi,dest]
  rw [expand, Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro sel _
  rw [← Finset.sum_filter, Finset.sum_const, ← selected_count adj s t hs S sel]
  have hzero : (((selectedGraph adj S s sel).hamPaths s t).card : ZMod 2) = 0 :=
    ZMod.natCast_eq_zero_iff_even.mpr (Nat.not_odd_iff_even.mp (h sel))
  rw [← Nat.cast_smul_eq_nsmul (ZMod 2), hzero, zero_smul]

include hs in
/-- Push the nonvanishing event into the event of a selection with odd parity. -/
private theorem prob_le (d : ℕ) (hd : 2 ≤ d) :
    copyProb (adj := adj) d (fun S => pathPoly adj s t S ≠ 0) ≤
      copyProb (adj := adj) d (fun S => ∃ sel : Vertex s → Fin d,
        Odd ((selectedGraph adj S s sel).hamPaths s t).card) := by
  classical
  unfold copyProb
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro S hS
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hS ⊢
    exact good_of_nonzero adj s t hs S hS
  · intro S _ _
    apply Finset.prod_nonneg
    intro a _
    have hd' : 1 < (2:ℝ)^d := one_lt_pow₀ (by norm_num) (by omega)
    have hδ : delta d ≤ 1 := by unfold delta; apply div_le_one_of_le₀ <;> nlinarith [sq_nonneg ((2:ℝ)^d-1)]
    unfold copySetProb
    split_ifs
    · unfold delta; positivity
    · exact div_nonneg (sub_nonneg.mpr hδ) (by linarith)

end DHCSelections

open Classical in
theorem solution {V : Type} [Fintype V] [DecidableEq V] (adj : V → V → Prop)
    [DecidableRel adj] (s t : V) (hst : s ≠ t) (hloop : ∀ v, ¬ adj v v) (hs : ∀ u, ¬ adj u s)
    (ht : ∀ v, ¬ adj t v) (d : ℕ) (hd : 2 ≤ d) (hham : ((ofAdj adj).hamPaths s t).Nonempty) :
    (1 - delta d) ^ (Fintype.card V - 1) ≤
      copyProb (adj := adj) d (fun S => ∃ sel : {v // v ≠ s} → Fin d,
        Odd ((selectedGraph adj S s sel).hamPaths s t).card) := by
  exact (DirectedHamiltonicity.Main.lemma5 adj s t hst hloop hs ht d hd hham).trans
    (DHCSelections.prob_le adj s t hs d hd)

