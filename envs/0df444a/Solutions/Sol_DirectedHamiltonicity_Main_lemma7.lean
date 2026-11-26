-- Prove2me | solution 1 for DirectedHamiltonicity.Main.lemma7
-- status  : ACCEPTED   (prove)
-- author  : @Soh Kumabe
-- created : 2026-11-26T06:45:58.245956+00:00
-- url     : https://prove2.me/submissions/61329c07-16ec-425d-8038-07f1bba3c71d

import Definitions.Def_DirectedHamiltonicity_Main_Graphs

open DirectedHamiltonicity.Main DirectedHamiltonicity.Main.Multidigraph
open scoped BigOperators Matrix

namespace DHCTree

private abbrev R := Polynomial (ZMod 2)
variable {V E : Type} [Fintype V] [DecidableEq V]
private abbrev Nonroot (s : V) := {u : V // u ≠ s}
private def Reaches (s : V) (f : V → V) (x : V) := ∃ n : ℕ, f^[n] x = s
private noncomputable def transition (s : V) (f : V → V) : Matrix (Nonroot s) (Nonroot s) R :=
  Matrix.of fun i j => if i.1 = f j.1 then 1 else 0

omit [Fintype V] [DecidableEq V] in
private theorem reaches_step {s : V} {f : V → V} (hs : f s = s) (x : V) :
    Reaches s f x ↔ Reaches s f (f x) := by
  constructor
  · rintro ⟨n,h⟩
    exact ⟨n, by rw [← Function.iterate_succ_apply, Function.iterate_succ_apply', h, hs]⟩
  · rintro ⟨n,h⟩
    exact ⟨n+1, by simpa [Function.iterate_succ_apply] using h⟩

/-- If every parent chain reaches s, depth orders the selected columns into
triangular blocks, with the identity on each diagonal block. -/
private theorem det_reaches (s : V) (f : V → V) (hg : ∀ x, Reaches s f x) :
    (1 - transition s f).det = 1 := by
  classical
  let d := fun x => Nat.find (hg x)
  have lower (v : Nonroot s) : d (f v.1) < d v.1 := by
    have h : f^[d v.1] v.1 = s := Nat.find_spec (hg _)
    generalize hd : d v.1 = n at h ⊢
    cases n with
    | zero => exact (v.2 h).elim
    | succ n =>
      exact Nat.lt_succ_of_le (Nat.find_min' (hg _) (by simpa [Function.iterate_succ_apply] using h))
  let depth := fun v : Nonroot s => d v.1
  have htri : (1 - transition s f).BlockTriangular depth := by
    intro i j hij
    have hij' : i ≠ j := fun h => (h ▸ hij).false
    have hpar : i.1 ≠ f j.1 := by
      intro h
      exact (not_lt_of_gt hij) (show depth i < depth j by simpa [depth, h] using lower j)
    simp [Matrix.sub_apply, transition, hij', hpar]
  rw [htri.det]
  apply Finset.prod_eq_one
  intro level _
  suffices h : (1 - transition s f).toSquareBlock depth level = 1 by rw [h, Matrix.det_one]
  apply Matrix.ext
  intro i j
  have hpar : i.1.1 ≠ f j.1.1 := by
    intro h
    have hh := lower j.1
    change d (f j.1.1) < depth j.1 at hh
    rw [← h] at hh
    exact (not_lt_of_ge (le_of_eq (j.2.trans i.2.symm))) hh
  change (1 - transition s f) i.1 j.1 = _
  by_cases h : i = j
  · subst j; simp [transition, hpar]
  · have h' : i.1 ≠ j.1 := fun x => h (Subtype.ext x)
    simp [transition, h, h', hpar]

/-- The indicator of the vertices that never reach s lies in the left kernel. -/
private theorem det_misses (s : V) (f : V → V) (hs : f s = s)
    (hg : ¬ ∀ x, Reaches s f x) : (1 - transition s f).det = 0 := by
  classical
  let u (j : Nonroot s) : R := if Reaches s f j.1 then 0 else 1
  have hroot : Reaches s f s := ⟨0,rfl⟩
  apply Matrix.exists_vecMul_eq_zero_iff.mp
  refine ⟨u, ?_, ?_⟩
  · intro hz
    obtain ⟨x,hx⟩ := not_forall.mp hg
    let j : Nonroot s := ⟨x, fun h => hx (h ▸ hroot)⟩
    simpa [u, j, hx] using congrFun hz j
  · rw [Matrix.vecMul_sub, Matrix.vecMul_one, sub_eq_zero]
    funext j
    simp only [Matrix.vecMul_apply, dotProduct, transition]
    by_cases hp : f j.1 = s
    · have hj : Reaches s f j.1 := (reaches_step hs _).2 (by rw [hp]; exact hroot)
      have hm (i : Nonroot s) : i.1 ≠ f j.1 := fun h => i.2 (h.trans hp)
      simp [hm, u, hj]
    · let k : Nonroot s := ⟨f j.1,hp⟩
      rw [Finset.sum_eq_single k]
      · have he := reaches_step hs j.1
        simp [u, k, he]
      · intro i _ hi
        have hm : i.1 ≠ f j.1 := fun h => hi (Subtype.ext h)
        simp [hm]
      · simp

variable (H : Multidigraph V E) (s : V)
private abbrev Choice := (v : Nonroot s) → {e : E // H.head e = v.1}
private def parent (a : Choice H s) (v : V) : V := if h : v ≠ s then H.tail (a ⟨v,h⟩).1 else s
private noncomputable def chosen (a : Choice H s) : Finset E := by
  classical exact Finset.univ.image (fun v => (a v).1)

private theorem chosen_mem (a : Choice H s) (e : E) :
    e ∈ chosen H s a ↔ ∃ i, (a i).1 = e := by classical simp [chosen]

private theorem chosen_edge (a : Choice H s) (u v : V) :
    (∃ e ∈ chosen H s a, H.tail e = u ∧ H.head e = v) ↔
      v ≠ s ∧ parent H s a v = u := by
  classical
  constructor
  · rintro ⟨e,he,ht,hh⟩
    obtain ⟨i,rfl⟩ := (chosen_mem H s a e).1 he
    have hv : i.1 = v := (a i).2.symm.trans hh
    rw [← hv]
    exact ⟨i.2, by simpa only [parent, dif_pos i.2] using ht⟩
  · rintro ⟨hv,hu⟩
    let i : Nonroot s := ⟨v,hv⟩
    exact ⟨(a i).1, (chosen_mem H s a _).2 ⟨i,rfl⟩, by simpa [parent,hv,i] using hu, (a i).2⟩

private theorem chosen_tree (a : Choice H s) :
    H.IsOutArborescence s (chosen H s a) ↔ ∀ v, Reaches s (parent H s a) v := by
  classical
  let f := parent H s a
  have hs : f s = s := by simp [f, parent]
  have hreach (v : V) :
      Relation.ReflTransGen (fun u v => ∃ e ∈ chosen H s a, H.tail e = u ∧ H.head e = v) s v ↔
        Reaches s f v := by
    constructor
    · intro h
      induction h with
      | refl => exact ⟨0,rfl⟩
      | tail _ step ih =>
        obtain ⟨_,hh⟩ := (chosen_edge H s a _ _).1 step
        exact (reaches_step hs _).2 (by change Reaches s f (parent H s a _); rw [hh]; exact ih)
    · rintro ⟨n,hn⟩
      induction n generalizing v with
      | zero => have hv : v = s := hn; subst v; exact .refl
      | succ n ih =>
        by_cases hv : v = s
        · subst v; exact .refl
        · exact (ih (f v) (by simpa [Function.iterate_succ_apply] using hn)).tail
            ((chosen_edge H s a _ _).2 ⟨hv,rfl⟩)
  constructor
  · exact fun ht v => (hreach v).1 (ht.2.2 v)
  · intro hgood
    refine ⟨?_, ?_, fun v => (hreach v).2 (hgood v)⟩
    · intro e he
      obtain ⟨i,rfl⟩ := (chosen_mem H s a e).1 he
      rw [(a i).2]
      exact i.2
    · intro v hv
      let i : Nonroot s := ⟨v,hv⟩
      refine ⟨(a i).1, ⟨(chosen_mem H s a _).2 ⟨i,rfl⟩, (a i).2⟩, ?_⟩
      rintro e ⟨he,hh⟩
      obtain ⟨j,rfl⟩ := (chosen_mem H s a e).1 he
      have hji : j = i := Subtype.ext ((a j).2.symm.trans hh)
      rw [hji]


variable [Fintype E] [DecidableEq E]

private noncomputable def term (w : E → R) (i j : Nonroot s) (e : E) : R :=
  w e * ((if i = j then 1 else 0) - if i.1 = H.tail e then 1 else 0)

omit [Fintype V] [DecidableEq E] in
private theorem lap_column (w : E → R) (hl : H.Loopless) (i j : Nonroot s) :
    (H.reducedLaplacian w s) i j =
      ∑ e : {e // H.head e = j.1}, term H s w i j e.1 := by
  classical
  let U := Finset.univ.filter (fun e => H.head e = j.1)
  have hU : ∀ e, e ∈ U ↔ H.head e = j.1 := by simp [U]
  rw [← Finset.sum_subtype U hU]
  simp only [reducedLaplacian, Matrix.submatrix_apply, laplacian, U, Finset.sum_filter]
  by_cases hij : i = j
  · subst j
    simp only [if_true]
    apply Finset.sum_congr rfl
    intro e _
    by_cases hh : H.head e = i.1
    · have ht : i.1 ≠ H.tail e := fun h => hl e (h.symm.trans hh.symm)
      simp [term, hh, ht]
    · simp [hh]
  · have hv : i.1 ≠ j.1 := fun h => hij (Subtype.ext h)
    rw [if_neg hv, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro e _
    simp only [term, if_neg hij, zero_sub, neg_ite, neg_zero,
      show (i.1 = H.tail e) ↔ (H.tail e = i.1) from eq_comm]
    by_cases hh : H.head e = j.1 <;> by_cases ht : H.tail e = i.1 <;> simp [hh, ht]

/-- Multilinearity of the determinant in all columns at once. -/
private theorem det_column_sum {I : Type} [Fintype I] [DecidableEq I] {J : I → Type}
    [∀ i, Fintype (J i)] (A : (i j : I) → J j → R) :
    (Matrix.of fun i j => ∑ e, A i j e).det =
      ∑ a : (j : I) → J j, (Matrix.of fun i j => A i j (a j)).det := by
  classical
  simp only [Matrix.det_apply', Matrix.of_apply, Fintype.prod_sum, Finset.mul_sum]
  rw [Finset.sum_comm]

omit [Fintype E] [DecidableEq E] in
open Classical in
private theorem selected_det (w : E → R) (a : Choice H s) :
    (Matrix.of fun i j => term H s w i j (a j).1).det =
      if H.IsOutArborescence s (chosen H s a) then ∏ j, w (a j).1 else 0 := by
  classical
  let f := parent H s a
  have hs : f s = s := by simp [f, parent]
  have hm : (Matrix.of fun i j => term H s w i j (a j).1) =
      Matrix.of (fun i j => w (a j).1 * (1 - transition s f) i j) := by
    ext i j
    simp [term, transition, f, parent, j.2, Matrix.one_apply]
  rw [hm, Matrix.det_mul_row, chosen_tree]
  split_ifs with hg
  · rw [det_reaches s f hg, mul_one]
  · rw [det_misses s f hs hg, mul_zero]

omit [Fintype E] [DecidableEq E] in
private theorem chosen_injective : Function.Injective (chosen H s) := by
  classical
  intro a b hab
  funext i
  apply Subtype.ext
  have hi : (a i).1 ∈ chosen H s b := hab ▸ (chosen_mem H s a _).2 ⟨i,rfl⟩
  obtain ⟨j,hj⟩ := (chosen_mem H s b _).1 hi
  have hji : j = i := Subtype.ext ((b j).2.symm.trans ((congrArg H.head hj).trans (a i).2))
  exact hji ▸ hj.symm

omit [Fintype E] [DecidableEq E] in
private theorem represents (T : Finset E) (ht : H.IsOutArborescence s T) :
    ∃ a : Choice H s, chosen H s a = T := by
  classical
  let e (v : Nonroot s) := Classical.choose (ht.2.1 v.1 v.2)
  have he (v : Nonroot s) := Classical.choose_spec (ht.2.1 v.1 v.2)
  let a : Choice H s := fun v => ⟨e v, (he v).1.2⟩
  refine ⟨a, ?_⟩
  ext k
  rw [chosen_mem]
  constructor
  · rintro ⟨v,rfl⟩
    exact (he v).1.1
  · intro hk
    let v : Nonroot s := ⟨H.head k,ht.1 k hk⟩
    exact ⟨v, ((he v).2 k ⟨hk,rfl⟩).symm⟩

end DHCTree

open DHCTree
open Classical in
set_option maxHeartbeats 800000 in
theorem solution {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (H : Multidigraph V E) (hH : H.Loopless) (p : E → Polynomial (ZMod 2)) (s : V) :
    (H.reducedLaplacian p s).det =
      ∑ T ∈ Finset.univ.filter (fun T : Finset E => H.IsOutArborescence s T), ∏ e ∈ T, p e := by
  classical
  have hM : H.reducedLaplacian p s = Matrix.of (fun i j => ∑ e : {e // H.head e = j.1},
      term H s p i j e.1) := Matrix.ext (lap_column H s p hH)
  rw [hM, det_column_sum]
  simp_rw [selected_det H s p]
  rw [← Finset.sum_filter]
  apply Finset.sum_bij (fun a _ => chosen H s a)
  · intro a ha
    simpa using ha
  · intro a _ b _ hab
    exact chosen_injective H s hab
  · intro T hT
    obtain ⟨a,ha⟩ := represents H s T (Finset.mem_filter.mp hT).2
    exact ⟨a, by simpa [ha] using hT, ha⟩
  · intro a _
    let _ : DecidableEq E := Classical.typeDecidableEq E
    rw [chosen, Finset.prod_image]
    intro i _ j _ h
    exact Subtype.ext ((a i).2.symm.trans ((congrArg H.head h).trans (a j).2))


