-- Prove2me | solution 1 for Chou.fg_of_isVirtuallyPolycyclic_quotient_of_not_hasFreeSubsemigroupOfRankTwo
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-20T13:22:21.997213+00:00
-- url     : https://prove2.me/submissions/9fa4a3b7-f98e-43c4-9ca8-b30c01a53ddc

import Definitions.Def_Chou_Growth
import Definitions.Def_MilnorWolf_Growth
import Mathlib

/-!
# Rosenblatt's Lemma 4.8 and the virtually polycyclic quotient

Rosenblatt, *Invariant measures and growth conditions*, Trans. Amer. Math. Soc. 193 (1974),
Lemma 4.8 (p. 42), Lemma 4.9 (p. 43) and Lemma 4.10 (p. 44); Milnor, *Growth of finitely
generated solvable groups*, J. Differential Geometry 2 (1968) 447–449, Lemmas 1–3; Chou,
*Elementary amenable groups*, Illinois J. Math. 24 (1980) 400–401.

Rosenblatt's Lemma 4.8 is Milnor's Lemma 1 with "no free subsemigroup on two generators" in
place of "not of exponential growth": in a group with no free subsemigroup of rank two, the
conjugates `β ^ k * α * β ^ (-k)`, `k ∈ ℤ`, span a finitely generated subgroup — and, the
hypothesis being used through the single pair `β, β α`, not even finite generation is needed for
that lemma.
Rosenblatt states it for `A` abelian; as Chou remarks (p. 400, and p. 401 "with the understanding
that `A` doesn't have to be abelian there") the abelian hypothesis is not needed, and the proof
below has none: the ordered products `α_1^{i₁} ⋯ α_m^{i_m}` are `List.prod`s and the relation is
solved at its last and at its first index of disagreement.

The input that replaces Milnor's counting argument is Rosenblatt's opening paragraph on p. 42:
from a pair of *distinct* words in `x, y` with the same value one produces a pair of distinct
words *of the same length* with the same value, by replacing `W₁ ≠ W₂` with `W₁W₂` and `W₂W₁`
after cancelling the common prefix.

The assembly then runs by induction along a polycyclic series, not by Rosenblatt's tower of
conjugates (4.10), whose finiteness uses that `A` is abelian: a finite cyclic step is a finite
index step, handled by Schreier, and an infinite cyclic step is a surjection onto `ℤ`, handled by
Lemma 4.8 in the shape of Milnor's Lemma 1.
-/

universe u

namespace Chou
namespace Rbt

open Chou

/-! ### The conjugates `β ^ k * α * β ^ (-k)` -/

section Conj

variable {B : Type*} [Group B]

/-- `mconj α β k = β ^ k * α * β ^ (-k)`, Milnor's `α_k`. -/
def mconj (α β : B) (k : ℤ) : B := β ^ k * α * β ^ (-k)

lemma mconj_succ (α β : B) (k : ℤ) : mconj α β (k + 1) = β * mconj α β k * β⁻¹ := by
  simp only [mconj, zpow_neg]
  group

lemma mconj_pred (α β : B) (k : ℤ) : mconj α β (k - 1) = β⁻¹ * mconj α β k * β := by
  simp only [mconj, zpow_neg]
  group

lemma mconj_pow (α β : B) (k : ℤ) (m : ℕ) :
    mconj α β k ^ m = β ^ k * α ^ m * (β ^ k)⁻¹ := by
  simp only [mconj, zpow_neg]
  induction m with
  | zero => simp
  | succ m ih =>
      rw [pow_succ, ih, pow_succ]
      group

@[simp] lemma mconj_zero' (α β : B) : mconj α β 0 = α := by simp [mconj]

end Conj

/-! ### Milnor's words `β α^{i₀} β α^{i₁} ⋯` and their normal form -/

section Words

variable {B : Type*} [Group B]

/-- Milnor's word `β α^{i 0} · β α^{i 1} ⋯ β α^{i (n-1)}`. -/
def wrd (α β : B) (i : ℕ → ℕ) (n : ℕ) : B :=
  ((List.range n).map (fun k => β * α ^ i k)).prod

/-- The `k`-th factor `α_{k+1} ^ (i k)` of Milnor's product. -/
def mfac (α β : B) (i : ℕ → ℕ) (k : ℕ) : B := mconj α β ((k : ℤ) + 1) ^ i k

/-- The ordered product `∏_{k ∈ L} α_{k+1} ^ (i k)` of Milnor's conjugates. -/
def wseg (α β : B) (i : ℕ → ℕ) (L : List ℕ) : B := (L.map (mfac α β i)).prod

@[simp] lemma wseg_nil (α β : B) (i : ℕ → ℕ) : wseg α β i [] = 1 := rfl

lemma wseg_cons (α β : B) (i : ℕ → ℕ) (k : ℕ) (L : List ℕ) :
    wseg α β i (k :: L) = mconj α β ((k : ℤ) + 1) ^ i k * wseg α β i L := by
  rw [wseg, List.map_cons, List.prod_cons, wseg, mfac]

lemma wseg_append (α β : B) (i : ℕ → ℕ) (L₁ L₂ : List ℕ) :
    wseg α β i (L₁ ++ L₂) = wseg α β i L₁ * wseg α β i L₂ := by
  rw [wseg, List.map_append, List.prod_append, wseg, wseg]

lemma wseg_congr (α β : B) {i j : ℕ → ℕ} {L : List ℕ} (h : ∀ k ∈ L, i k = j k) :
    wseg α β i L = wseg α β j L := by
  rw [wseg, wseg]
  congr 1
  refine List.map_congr_left ?_
  intro k hk
  rw [mfac, mfac, h k hk]

/-- Every ordered product of conjugates with indices in `X` lies in the subgroup they span. -/
lemma wseg_mem_closure (α β : B) (i : ℕ → ℕ) (X : Set ℤ) :
    ∀ L : List ℕ, (∀ k ∈ L, ((k : ℤ) + 1) ∈ X) →
      wseg α β i L ∈ Subgroup.closure (mconj α β '' X) := by
  intro L
  induction L with
  | nil => intro _; simp
  | cons k L ih =>
      intro hL
      rw [wseg_cons]
      refine Subgroup.mul_mem _ (Subgroup.pow_mem _ ?_ _) (ih fun m hm => hL m (by simp [hm]))
      exact Subgroup.subset_closure ⟨(k : ℤ) + 1, hL k (by simp), rfl⟩

/-- Milnor's normal form (p. 448): `β α^{i 0} ⋯ β α^{i (n-1)} = α_1^{i 0} ⋯ α_n^{i (n-1)} β^n`,
with the product on the right an *ordered* product — no commutativity is used. -/
lemma wrd_eq (α β : B) (i : ℕ → ℕ) (n : ℕ) :
    wrd α β i n = wseg α β i (List.range n) * β ^ n := by
  induction n with
  | zero => simp [wrd, wseg]
  | succ n ih =>
      have hz : (β : B) ^ ((n : ℤ) + 1) = β ^ (n + 1) := by
        rw [← zpow_natCast β (n + 1)]
        norm_cast
      have hstep : β ^ n * (β * α ^ i n)
          = mconj α β ((n : ℤ) + 1) ^ i n * β ^ (n + 1) := by
        rw [mconj_pow, hz, pow_succ]
        group
      rw [wrd, List.range_succ, List.map_append, List.prod_append, ← wrd, ih, wseg_append,
        wseg_cons, wseg_nil, mul_one]
      simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
      rw [mul_assoc, hstep, ← mul_assoc]

end Words

/-! ### Exploiting the relation, without commutativity -/

section Relation

variable {B : Type*} [Group B]

/-- Solving for the conjugate at the right-hand end of the relation. -/
lemma mconj_mem_closure_last (α β : B) (u v : ℕ → ℕ) (L : List ℕ) (X : Set ℤ)
    (hL : ∀ k ∈ L, ((k : ℤ) + 1) ∈ X) (r : ℕ) (hu : u r = 1) (hv : v r = 0)
    (h : wseg α β u (L ++ [r]) = wseg α β v (L ++ [r])) :
    mconj α β ((r : ℤ) + 1) ∈ Subgroup.closure (mconj α β '' X) := by
  simp only [wseg_append, wseg_cons, wseg_nil, mul_one, hu, hv, pow_one, pow_zero] at h
  have hm : mconj α β ((r : ℤ) + 1) = (wseg α β u L)⁻¹ * wseg α β v L := by
    rw [← h]; group
  rw [hm]
  exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (wseg_mem_closure α β u X L hL))
    (wseg_mem_closure α β v X L hL)

/-- Solving for the conjugate at the left-hand end of the relation. -/
lemma mconj_mem_closure_head (α β : B) (u v : ℕ → ℕ) (L : List ℕ) (X : Set ℤ)
    (hL : ∀ k ∈ L, ((k : ℤ) + 1) ∈ X) (r : ℕ) (hu : u r = 1) (hv : v r = 0)
    (h : wseg α β u (r :: L) = wseg α β v (r :: L)) :
    mconj α β ((r : ℤ) + 1) ∈ Subgroup.closure (mconj α β '' X) := by
  simp only [wseg_cons, hu, hv, pow_one, pow_zero, one_mul] at h
  have hm : mconj α β ((r : ℤ) + 1) = wseg α β v L * (wseg α β u L)⁻¹ := by
    rw [← h]; group
  rw [hm]
  exact Subgroup.mul_mem _ (wseg_mem_closure α β v X L hL)
    (Subgroup.inv_mem _ (wseg_mem_closure α β u X L hL))

end Relation

/-! ### From a window of conjugates to all of them -/

section Fg

variable {B : Type*} [Group B]

/-- Conjugating by `β` shifts indices up by one. -/
lemma conj_closure_succ (α β : B) (X Y : Set ℤ)
    (hXY : ∀ k ∈ X, mconj α β (k + 1) ∈ Subgroup.closure (mconj α β '' Y)) {x : B}
    (hx : x ∈ Subgroup.closure (mconj α β '' X)) :
    β * x * β⁻¹ ∈ Subgroup.closure (mconj α β '' Y) := by
  induction hx using Subgroup.closure_induction with
  | mem y hy =>
      obtain ⟨k, hk, rfl⟩ := hy
      rw [← mconj_succ]
      exact hXY k hk
  | one => simp
  | mul y z _ _ ihy ihz =>
      have hyz : β * (y * z) * β⁻¹ = (β * y * β⁻¹) * (β * z * β⁻¹) := by group
      rw [hyz]
      exact Subgroup.mul_mem _ ihy ihz
  | inv y _ ihy =>
      have hy' : β * y⁻¹ * β⁻¹ = (β * y * β⁻¹)⁻¹ := by group
      rw [hy']
      exact Subgroup.inv_mem _ ihy

/-- Conjugating by `β⁻¹` shifts indices down by one. -/
lemma conj_closure_pred (α β : B) (X Y : Set ℤ)
    (hXY : ∀ k ∈ X, mconj α β (k - 1) ∈ Subgroup.closure (mconj α β '' Y)) {x : B}
    (hx : x ∈ Subgroup.closure (mconj α β '' X)) :
    β⁻¹ * x * β ∈ Subgroup.closure (mconj α β '' Y) := by
  induction hx using Subgroup.closure_induction with
  | mem y hy =>
      obtain ⟨k, hk, rfl⟩ := hy
      rw [← mconj_pred]
      exact hXY k hk
  | one => simp
  | mul y z _ _ ihy ihz =>
      have hyz : β⁻¹ * (y * z) * β = (β⁻¹ * y * β) * (β⁻¹ * z * β) := by group
      rw [hyz]
      exact Subgroup.mul_mem _ ihy ihz
  | inv y _ ihy =>
      have hy' : β⁻¹ * y⁻¹ * β = (β⁻¹ * y * β)⁻¹ := by group
      rw [hy']
      exact Subgroup.inv_mem _ ihy

/-- If the conjugate at the top of a window lies in the subgroup generated by the window minus
its top, and symmetrically at the bottom, then all conjugates lie in the subgroup generated by
the window, which is therefore finitely generated. -/
lemma fg_closure_range_mconj (α β : B) (P Q : ℤ) (hPQ : P ≤ Q)
    (htop : mconj α β Q ∈ Subgroup.closure (mconj α β '' Set.Icc P (Q - 1)))
    (hbot : mconj α β P ∈ Subgroup.closure (mconj α β '' Set.Icc (P + 1) Q)) :
    (Subgroup.closure (Set.range (mconj α β))).FG := by
  classical
  have hup : ∀ x ∈ Subgroup.closure (mconj α β '' Set.Icc P Q),
      β * x * β⁻¹ ∈ Subgroup.closure (mconj α β '' Set.Icc P Q) := by
    intro x hx
    refine conj_closure_succ α β (Set.Icc P Q) (Set.Icc P Q) ?_ hx
    intro k hk
    rw [Set.mem_Icc] at hk
    by_cases hkQ : k = Q
    · rw [hkQ, mconj_succ]
      refine conj_closure_succ α β (Set.Icc P (Q - 1)) (Set.Icc P Q) ?_ htop
      intro m hm
      rw [Set.mem_Icc] at hm
      exact Subgroup.subset_closure ⟨m + 1, Set.mem_Icc.mpr ⟨by omega, by omega⟩, rfl⟩
    · exact Subgroup.subset_closure ⟨k + 1, Set.mem_Icc.mpr ⟨by omega, by omega⟩, rfl⟩
  have hdown : ∀ x ∈ Subgroup.closure (mconj α β '' Set.Icc P Q),
      β⁻¹ * x * β ∈ Subgroup.closure (mconj α β '' Set.Icc P Q) := by
    intro x hx
    refine conj_closure_pred α β (Set.Icc P Q) (Set.Icc P Q) ?_ hx
    intro k hk
    rw [Set.mem_Icc] at hk
    by_cases hkP : k = P
    · rw [hkP, mconj_pred]
      refine conj_closure_pred α β (Set.Icc (P + 1) Q) (Set.Icc P Q) ?_ hbot
      intro m hm
      rw [Set.mem_Icc] at hm
      exact Subgroup.subset_closure ⟨m - 1, Set.mem_Icc.mpr ⟨by omega, by omega⟩, rfl⟩
    · exact Subgroup.subset_closure ⟨k - 1, Set.mem_Icc.mpr ⟨by omega, by omega⟩, rfl⟩
  have hbase : mconj α β P ∈ Subgroup.closure (mconj α β '' Set.Icc P Q) :=
    Subgroup.subset_closure ⟨P, Set.mem_Icc.mpr ⟨le_refl P, hPQ⟩, rfl⟩
  have hshift : ∀ j : ℤ, mconj α β (P + j) ∈ Subgroup.closure (mconj α β '' Set.Icc P Q) := by
    intro j
    induction j with
    | zero => simpa using hbase
    | succ i ih =>
        have hEq : P + ((i : ℤ) + 1) = (P + (i : ℤ)) + 1 := by ring
        rw [hEq, mconj_succ]
        exact hup _ ih
    | pred i ih =>
        have hEq : P + (-(i : ℤ) - 1) = (P + -(i : ℤ)) - 1 := by ring
        rw [hEq, mconj_pred]
        exact hdown _ ih
  have hall : ∀ k : ℤ, mconj α β k ∈ Subgroup.closure (mconj α β '' Set.Icc P Q) := by
    intro k
    have hk := hshift (k - P)
    simpa using hk
  have heq : Subgroup.closure (Set.range (mconj α β))
      = Subgroup.closure (mconj α β '' Set.Icc P Q) := by
    refine le_antisymm ?_ (Subgroup.closure_mono ?_)
    · rw [Subgroup.closure_le]
      rintro x ⟨k, rfl⟩
      exact hall k
    · rintro x ⟨k, -, rfl⟩
      exact ⟨k, rfl⟩
  rw [heq]
  refine ⟨(Finset.Icc P Q).image (mconj α β), ?_⟩
  rw [Finset.coe_image, Finset.coe_Icc]

end Fg

/-! ### Milnor's Lemma 1 from a collision of two words of the same length -/

/-- The core of Milnor's Lemma 1 (p. 447–448), with the source of the relation abstracted: if two
*distinct* `{0,1}`-valued exponent sequences, both vanishing from `n` on, give the same word
`β α^{i 0} ⋯ β α^{i (n-1)}`, then the conjugates `β ^ k * α * β ^ (-k)` span a finitely generated
subgroup.  No commutativity and no growth hypothesis enter here. -/
theorem fg_closure_range_mconj_of_collision {B : Type*} [Group B] (α β : B) {n : ℕ}
    {u v : ℕ → ℕ} (hu1 : ∀ k, u k ≤ 1) (hv1 : ∀ k, v k ≤ 1)
    (hzeroU : ∀ k, n ≤ k → u k = 0) (hzeroV : ∀ k, n ≤ k → v k = 0) (huv : u ≠ v)
    (hfg : wrd α β u n = wrd α β v n) :
    (Subgroup.closure (Set.range (mconj α β))).FG := by
  classical
  set D : Finset ℕ := (Finset.range n).filter (fun k => u k ≠ v k) with hDdef
  have hDne : D.Nonempty := by
    by_contra hc
    rw [Finset.not_nonempty_iff_eq_empty] at hc
    apply huv
    funext k
    by_cases hk : k < n
    · by_contra hne'
      have hmem : k ∈ D := by rw [hDdef, Finset.mem_filter, Finset.mem_range]; exact ⟨hk, hne'⟩
      rw [hc] at hmem
      simp at hmem
    · rw [hzeroU k (by omega), hzeroV k (by omega)]
  set p : ℕ := D.min' hDne with hpdef
  set q : ℕ := D.max' hDne with hqdef
  have hpD : p ∈ D := D.min'_mem hDne
  have hqD : q ∈ D := D.max'_mem hDne
  have hpq : p ≤ q := D.min'_le q hqD
  have hqn : q < n := Finset.mem_range.mp (Finset.mem_filter.mp hqD).1
  have hupne : u p ≠ v p := (Finset.mem_filter.mp hpD).2
  have huqne : u q ≠ v q := (Finset.mem_filter.mp hqD).2
  have hagree : ∀ k, k < n → (k < p ∨ q < k) → u k = v k := by
    intro k hk hc
    by_contra hne'
    have hmem : k ∈ D := by rw [hDdef, Finset.mem_filter, Finset.mem_range]; exact ⟨hk, hne'⟩
    rcases hc with hc | hc
    · exact absurd (D.min'_le k hmem) (by omega)
    · exact absurd (D.le_max' k hmem) (by omega)
  -- the relation between the two ordered products
  have hrel : wseg α β u (List.range n) = wseg α β v (List.range n) := by
    have h1 := wrd_eq α β u n
    have h2 := wrd_eq α β v n
    rw [h1, h2] at hfg
    exact mul_right_cancel hfg
  -- cut the common prefix and the common suffix
  have e1 : List.range' p (q + 1 - p) ++ List.range' (q + 1) (n - (q + 1))
      = List.range' p (n - p) := by
    have h0 := List.range'_append_1 (s := p) (m := q + 1 - p) (n := n - (q + 1))
    rw [show p + (q + 1 - p) = q + 1 from by omega,
      show q + 1 - p + (n - (q + 1)) = n - p from by omega] at h0
    exact h0
  have e2 : List.range' 0 p ++ List.range' p (n - p) = List.range' 0 n := by
    have h0 := List.range'_append_1 (s := 0) (m := p) (n := n - p)
    rw [show 0 + p = p from by omega, show p + (n - p) = n from by omega] at h0
    exact h0
  have hsplit : List.range n
      = List.range' 0 p ++ (List.range' p (q + 1 - p) ++ List.range' (q + 1) (n - (q + 1))) := by
    rw [List.range_eq_range', ← e2, e1]
  have hmemA : ∀ k ∈ List.range' 0 p, u k = v k := by
    intro k hk
    rw [List.mem_range'_1] at hk
    exact hagree k (by omega) (Or.inl (by omega))
  have hmemE : ∀ k ∈ List.range' (q + 1) (n - (q + 1)), u k = v k := by
    intro k hk
    rw [List.mem_range'_1] at hk
    exact hagree k (by omega) (Or.inr (by omega))
  have hM : wseg α β u (List.range' p (q + 1 - p))
      = wseg α β v (List.range' p (q + 1 - p)) := by
    rw [hsplit, wseg_append, wseg_append, wseg_append, wseg_append,
      wseg_congr α β hmemA, wseg_congr α β hmemE] at hrel
    exact mul_right_cancel (mul_left_cancel hrel)
  -- the two ends of the relation
  have hMtop : List.range' p (q + 1 - p) = List.range' p (q - p) ++ [q] := by
    have h0 := List.range'_concat (s := p) (n := q - p) (step := 1)
    rw [show p + 1 * (q - p) = q from by omega] at h0
    rw [show q + 1 - p = q - p + 1 from by omega]
    exact h0
  have hMbot : List.range' p (q + 1 - p) = p :: List.range' (p + 1) (q - p) := by
    rw [show q + 1 - p = q - p + 1 from by omega]
    rfl
  have htop : mconj α β ((q : ℤ) + 1)
      ∈ Subgroup.closure (mconj α β '' Set.Icc ((p : ℤ) + 1) (((q : ℤ) + 1) - 1)) := by
    have hL : ∀ k ∈ List.range' p (q - p),
        ((k : ℤ) + 1) ∈ Set.Icc ((p : ℤ) + 1) (((q : ℤ) + 1) - 1) := by
      intro k hk
      rw [List.mem_range'_1] at hk
      have h1 : p ≤ k := hk.1
      have h2 : k < q := by omega
      exact Set.mem_Icc.mpr ⟨by omega, by omega⟩
    rcases Nat.lt_or_ge (u q) (v q) with hc | hc
    · have h1 : v q = 1 := by have := hv1 q; omega
      have h0 : u q = 0 := by omega
      exact mconj_mem_closure_last α β v u _ _ hL q h1 h0 (by rw [← hMtop]; exact hM.symm)
    · have h1 : u q = 1 := by have := hu1 q; omega
      have h0 : v q = 0 := by omega
      exact mconj_mem_closure_last α β u v _ _ hL q h1 h0 (by rw [← hMtop]; exact hM)
  have hbot : mconj α β ((p : ℤ) + 1)
      ∈ Subgroup.closure (mconj α β '' Set.Icc (((p : ℤ) + 1) + 1) ((q : ℤ) + 1)) := by
    have hL : ∀ k ∈ List.range' (p + 1) (q - p),
        ((k : ℤ) + 1) ∈ Set.Icc (((p : ℤ) + 1) + 1) ((q : ℤ) + 1) := by
      intro k hk
      rw [List.mem_range'_1] at hk
      have h1 : p + 1 ≤ k := hk.1
      have h2 : k ≤ q := by omega
      exact Set.mem_Icc.mpr ⟨by omega, by omega⟩
    rcases Nat.lt_or_ge (u p) (v p) with hc | hc
    · have h1 : v p = 1 := by have := hv1 p; omega
      have h0 : u p = 0 := by omega
      exact mconj_mem_closure_head α β v u _ _ hL p h1 h0 (by rw [← hMbot]; exact hM.symm)
    · have h1 : u p = 1 := by have := hu1 p; omega
      have h0 : v p = 0 := by omega
      exact mconj_mem_closure_head α β u v _ _ hL p h1 h0 (by rw [← hMbot]; exact hM)
  exact fg_closure_range_mconj α β ((p : ℤ) + 1) ((q : ℤ) + 1) (by omega) htop hbot

/-! ### The relation supplied by "no free subsemigroup on two generators" (Rosenblatt, p. 42) -/

section FreeSemigroup

variable {B : Type*} [Group B]

/-- The other of the two letters. -/
def other (c : Fin 2) : Fin 2 := if c = 0 then 1 else 0

lemma other_ne (c : Fin 2) : other c ≠ c := by
  fin_cases c <;> simp [other]

/-- Cancelling the common prefix of two distinct words with the same value: what is left is a
pair of distinct words with the same value which do not begin with the same letter. -/
lemma exists_strip (f : Fin 2 → B) :
    ∀ x y : List (Fin 2), (x.map f).prod = (y.map f).prod → x ≠ y →
      ∃ x' y' : List (Fin 2), (x'.map f).prod = (y'.map f).prod ∧ x' ≠ y' ∧
        x'.head? ≠ y'.head? := by
  intro x
  induction x with
  | nil =>
      intro y h hne
      refine ⟨[], y, h, hne, ?_⟩
      cases y with
      | nil => exact absurd rfl hne
      | cons a l => simp
  | cons c t ih =>
      intro y h hne
      match y with
      | [] => exact ⟨c :: t, [], h, hne, by simp⟩
      | (d :: s) =>
          by_cases hcd : c = d
          · subst hcd
            refine ih s ?_ ?_
            · simp only [List.map_cons, List.prod_cons] at h
              exact mul_left_cancel h
            · intro hts; exact hne (by rw [hts])
          · exact ⟨c :: t, d :: s, h, hne, by simp [hcd]⟩

/-- A nonempty word with value `1` gives two distinct words of the same length with the same
value: a block of the other letter, appended on the left and on the right. -/
lemma exists_eq_length_of_prod_eq_one (f : Fin 2 → B) (c : Fin 2) (t : List (Fin 2))
    (h : (((c :: t)).map f).prod = 1) :
    ∃ r s : List (Fin 2), r ≠ s ∧ r.length = s.length ∧ (r.map f).prod = (s.map f).prod := by
  refine ⟨(c :: t) ++ List.replicate (t.length + 1) (other c),
    List.replicate (t.length + 1) (other c) ++ (c :: t), ?_, ?_, ?_⟩
  · intro hEq
    have h1 : ((c :: t) ++ List.replicate (t.length + 1) (other c)).head? = some c := by simp
    have h2 : (List.replicate (t.length + 1) (other c) ++ (c :: t)).head? = some (other c) := by
      rw [List.replicate_succ]; simp
    rw [hEq, h2] at h1
    exact other_ne c (Option.some_injective _ h1)
  · simp only [List.length_append, List.length_replicate, List.length_cons]
  · simp only [List.map_append, List.prod_append, h, one_mul, mul_one]

/-- Rosenblatt, p. 42: a pair of elements generating no free subsemigroup satisfies a nontrivial
relation between two words of the *same length*.  From `W₁ ≠ W₂` with `W₁ = W₂` in the group one
passes to `W₁W₂` and `W₂W₁`, which have the same length and, after the common prefix has been
cancelled, begin with different letters. -/
lemma exists_eq_length_collision (f : Fin 2 → B)
    (h : ¬ Function.Injective (FreeMonoid.lift f)) :
    ∃ r s : List (Fin 2), r ≠ s ∧ r.length = s.length ∧ (r.map f).prod = (s.map f).prod := by
  rw [Function.not_injective_iff] at h
  obtain ⟨x, y, hxy, hne⟩ := h
  have hx : ((FreeMonoid.toList x).map f).prod = ((FreeMonoid.toList y).map f).prod := by
    simpa [FreeMonoid.lift_apply] using hxy
  have hne' : FreeMonoid.toList x ≠ FreeMonoid.toList y :=
    fun hc => hne (FreeMonoid.toList.injective hc)
  obtain ⟨a, b, hab, hne2, hhead⟩ := exists_strip f _ _ hx hne'
  match a, b, hab, hne2, hhead with
  | [], [], _, hne2, _ => exact absurd rfl hne2
  | [], (d :: s), hab, _, _ =>
      exact exists_eq_length_of_prod_eq_one f d s (by simpa using hab.symm)
  | (c :: t), [], hab, _, _ =>
      exact exists_eq_length_of_prod_eq_one f c t (by simpa using hab)
  | (c :: t), (d :: s), hab, _, hhead =>
      have hcd : c ≠ d := by
        intro hc; exact hhead (by simp [hc])
      refine ⟨(c :: t) ++ (d :: s), (d :: s) ++ (c :: t), ?_, ?_, ?_⟩
      · intro hEq
        have h1 : ((c :: t) ++ (d :: s)).head? = some c := by simp
        have h2 : ((d :: s) ++ (c :: t)).head? = some d := by simp
        rw [hEq, h2] at h1
        exact hcd (Option.some_injective _ h1).symm
      · simp only [List.length_append, List.length_cons]
        omega
      · simp only [List.map_append, List.prod_append, hab]

end FreeSemigroup

/-! ### Milnor's words read off a word in the two letters `β` and `β α` -/

section Bridge

variable {B : Type*} [Group B]

/-- A word in the letters `β` and `β α` is one of Milnor's words. -/
lemma wrd_eq_prod_map (α β : B) (w : List (Fin 2)) :
    wrd α β (fun k => ((w.getD k 0 : Fin 2) : ℕ)) w.length
      = (w.map (fun c : Fin 2 => β * α ^ (c : ℕ))).prod := by
  rw [wrd]
  congr 1
  refine List.ext_getElem (by simp) ?_
  intro i h₁ h₂
  have hi : i < w.length := by simpa using h₁
  rw [List.getElem_map, List.getElem_map, List.getElem_range, List.getD_eq_getElem w 0 hi]

/-- Milnor's Lemma 1 from a pair of distinct words of the same length in `β` and `β α` with the
same value. -/
theorem fg_closure_range_mconj_of_words (α β : B) (r s : List (Fin 2)) (hrs : r ≠ s)
    (hlen : r.length = s.length)
    (hprod : (r.map (fun c : Fin 2 => β * α ^ (c : ℕ))).prod
      = (s.map (fun c : Fin 2 => β * α ^ (c : ℕ))).prod) :
    (Subgroup.closure (Set.range (mconj α β))).FG := by
  refine fg_closure_range_mconj_of_collision (n := r.length)
    (u := fun k => ((r.getD k 0 : Fin 2) : ℕ)) (v := fun k => ((s.getD k 0 : Fin 2) : ℕ))
    α β (fun k => Nat.lt_succ_iff.mp (Fin.is_lt _)) (fun k => Nat.lt_succ_iff.mp (Fin.is_lt _))
    ?_ ?_ ?_ ?_
  · intro k hk
    rw [List.getD_eq_default r 0 hk]
    rfl
  · intro k hk
    rw [List.getD_eq_default s 0 (by omega)]
    rfl
  · intro hc
    refine hrs (List.ext_getElem hlen ?_)
    intro i h₁ h₂
    have hcc := congrFun hc i
    simp only [List.getD_eq_getElem r 0 h₁, List.getD_eq_getElem s 0 h₂] at hcc
    exact Fin.val_injective hcc
  · rw [wrd_eq_prod_map α β r, hlen, wrd_eq_prod_map α β s]
    exact hprod

/-- **Rosenblatt's Lemma 4.8** (Trans. Amer. Math. Soc. 193 (1974), p. 42), without the abelian
hypothesis: in a group with no free subsemigroup on two generators, the conjugates
`β ^ k * α * β ^ (-k)`, `k ∈ ℤ`, span a finitely generated subgroup.

Rosenblatt states it for an exact sequence `e → A → B → D → e` with `A` abelian, `a ∈ A`,
`b ∈ B`, concluding that `{b^k a b^{-k} : k ∈ ℤ}` spans a finitely generated subgroup of `A`; as
Chou observes (p. 400–401), the abelian hypothesis is used only to collect the two sides of the
relation into one product, and neither it nor the ambient normal subgroup is needed.  No finite
generation of the group is needed either: the hypothesis is used through a single pair of
elements. -/
theorem fg_closure_range_mconj_of_not_hasFreeSubsemigroupOfRankTwo {B : Type*} [Group B]
    (h : ¬ HasFreeSubsemigroupOfRankTwo B) (α β : B) :
    (Subgroup.closure (Set.range (mconj α β))).FG := by
  have hf : (![β, β * α] : Fin 2 → B) = fun c : Fin 2 => β * α ^ (c : ℕ) := by
    funext c
    fin_cases c <;> simp
  have hnot : ¬ Function.Injective (FreeMonoid.lift (fun c : Fin 2 => β * α ^ (c : ℕ))) := by
    intro hinj
    exact h ⟨β, β * α, by rw [hf]; exact hinj⟩
  obtain ⟨r, s, hrs, hlen, hprod⟩ := exists_eq_length_collision _ hnot
  exact fg_closure_range_mconj_of_words α β r s hrs hlen hprod

/-- Rosenblatt's Lemma 4.8 in the shape of the platform's Milnor Lemma 1. -/
theorem fg_closure_zpow_conj_of_not_hasFreeSubsemigroupOfRankTwo {B : Type*} [Group B]
    (h : ¬ HasFreeSubsemigroupOfRankTwo B) (α β : B) :
    (Subgroup.closure {x : B | ∃ k : ℤ, x = β ^ k * α * β ^ (-k)}).FG := by
  have hset : {x : B | ∃ k : ℤ, x = β ^ k * α * β ^ (-k)} = Set.range (mconj α β) := by
    ext x
    constructor
    · rintro ⟨k, rfl⟩; exact ⟨k, rfl⟩
    · rintro ⟨k, rfl⟩; exact ⟨k, rfl⟩
  rw [hset]
  exact fg_closure_range_mconj_of_not_hasFreeSubsemigroupOfRankTwo h α β

end Bridge

/-! ### Milnor's Lemma 1 assembled: the kernel of a surjection onto `ℤ`

Milnor's own assembly (p. 449) writes an arbitrary conjugate of `α_j` as
`(β₁^{i₁} ⋯ β_p^{i_p})⁻¹ α_j (β₁^{i₁} ⋯ β_p^{i_p})`, which uses both that the quotient is
polycyclic and that `A` is abelian, so that the `A`-part of the conjugator acts trivially; the
same step is Rosenblatt's in Lemma 4.10 (p. 44), where `A` is again abelian.  Neither hypothesis
is available here, so the assembly below is the one that needs neither: a finite generating set
of `B` is corrected by powers of `β` into a finite subset of the kernel, Lemma 4.8 is applied to
each correction, and the resulting finitely generated `β`-invariant subgroup `H` of the kernel
satisfies `H · ⟨β⟩ = B`, whence `H` is the kernel. -/

section Cyclic

variable {B : Type*} [Group B]

/-- Conjugation by all powers of `β`, from conjugation by `β` and by `β⁻¹`. -/
lemma zpow_conj_mem {H : Subgroup B} {β : B} (hup : ∀ x ∈ H, β * x * β⁻¹ ∈ H)
    (hdown : ∀ x ∈ H, β⁻¹ * x * β ∈ H) :
    ∀ (k : ℤ) (x : B), x ∈ H → β ^ k * x * (β ^ k)⁻¹ ∈ H := by
  intro k
  induction k using Int.induction_on with
  | zero => intro x hx; simpa using hx
  | succ i ih =>
      intro x hx
      have he : β ^ ((i : ℤ) + 1) * x * (β ^ ((i : ℤ) + 1))⁻¹
          = β * (β ^ (i : ℤ) * x * (β ^ (i : ℤ))⁻¹) * β⁻¹ := by
        rw [zpow_add, zpow_one]; group
      rw [he]
      exact hup _ (ih x hx)
  | pred i ih =>
      intro x hx
      have he : β ^ (-(i : ℤ) - 1) * x * (β ^ (-(i : ℤ) - 1))⁻¹
          = β⁻¹ * (β ^ (-(i : ℤ)) * x * (β ^ (-(i : ℤ)))⁻¹) * β := by
        rw [zpow_sub, zpow_one]; group
      rw [he]
      exact hdown _ (ih x hx)

/-- Lemma 4.8, applied to each member of a finite set at once. -/
lemma exists_finset_closure_biUnion (h : ¬ HasFreeSubsemigroupOfRankTwo B) (β : B) :
    ∀ T : Finset B, ∃ U : Finset B, Subgroup.closure (U : Set B)
      = Subgroup.closure (⋃ t ∈ (T : Set B), Set.range (mconj t β)) := by
  classical
  intro T
  induction T using Finset.induction_on with
  | empty => exact ⟨∅, by simp⟩
  | insert t T ht ih =>
      obtain ⟨U, hU⟩ := ih
      obtain ⟨V, hV⟩ := fg_closure_range_mconj_of_not_hasFreeSubsemigroupOfRankTwo h t β
      refine ⟨V ∪ U, ?_⟩
      rw [Finset.coe_union, Subgroup.closure_union, hU, hV, Finset.coe_insert,
        Set.biUnion_insert, Subgroup.closure_union]

/-- **Milnor's Lemma 1 in the form in which it is applied** (Milnor 1968, p. 449; Rosenblatt's
Lemma 4.8 supplies the input): in a finitely generated group with no free subsemigroup on two
generators, the kernel of a homomorphism onto `ℤ` is finitely generated.  No commutativity of the
kernel and no finite presentation of the quotient is needed. -/
theorem fg_ker_of_surjective_int [Group.FG B] (h : ¬ HasFreeSubsemigroupOfRankTwo B)
    (φ : B →* Multiplicative ℤ) (hφ : Function.Surjective φ) : Group.FG φ.ker := by
  classical
  obtain ⟨β, hβ⟩ := hφ (Multiplicative.ofAdd 1)
  have hpow : ∀ k : ℤ, φ (β ^ k) = Multiplicative.ofAdd k := by
    intro k
    rw [map_zpow, hβ, ← ofAdd_zsmul]
    norm_num
  obtain ⟨S, hS⟩ := Group.FG.out (G := B)
  set aa : B → B := fun s => s * (β ^ (Multiplicative.toAdd (φ s)))⁻¹ with haadef
  have haa_mem : ∀ s : B, aa s ∈ φ.ker := by
    intro s
    rw [MonoidHom.mem_ker, haadef]
    simp only [map_mul, map_inv, hpow]
    simp
  have hs_eq : ∀ s : B, s = aa s * β ^ (Multiplicative.toAdd (φ s)) := by
    intro s; rw [haadef]; group
  obtain ⟨U, hU⟩ := exists_finset_closure_biUnion h β (S.image aa)
  set H : Subgroup B := Subgroup.closure (U : Set B) with hHdef
  have hgen : ∀ s ∈ S, ∀ k : ℤ, mconj (aa s) β k ∈ H := by
    intro s hs k
    rw [hU]
    refine Subgroup.subset_closure (Set.mem_iUnion₂.mpr ⟨aa s, ?_, ⟨k, rfl⟩⟩)
    exact Finset.mem_coe.mpr (Finset.mem_image_of_mem aa hs)
  -- `H` lies in the kernel
  have hHker : H ≤ φ.ker := by
    rw [hU, Subgroup.closure_le]
    rintro x hx
    rw [Set.mem_iUnion₂] at hx
    obtain ⟨t, ht, k, rfl⟩ := hx
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp ht)
    have hc := (MonoidHom.normal_ker φ).conj_mem _ (haa_mem s) (β ^ k)
    simpa [mconj, zpow_neg] using hc
  -- `H` is invariant under conjugation by `β`
  have hup : ∀ x ∈ H, β * x * β⁻¹ ∈ H := by
    intro x hx
    rw [hU] at hx ⊢
    induction hx using Subgroup.closure_induction with
    | mem y hy =>
        rw [Set.mem_iUnion₂] at hy
        obtain ⟨t, ht, k, rfl⟩ := hy
        rw [← mconj_succ]
        exact Subgroup.subset_closure (Set.mem_biUnion ht ⟨k + 1, rfl⟩)
    | one => simp
    | mul y z _ _ ihy ihz =>
        have hyz : β * (y * z) * β⁻¹ = (β * y * β⁻¹) * (β * z * β⁻¹) := by group
        rw [hyz]; exact Subgroup.mul_mem _ ihy ihz
    | inv y _ ihy =>
        have hy' : β * y⁻¹ * β⁻¹ = (β * y * β⁻¹)⁻¹ := by group
        rw [hy']; exact Subgroup.inv_mem _ ihy
  have hdown : ∀ x ∈ H, β⁻¹ * x * β ∈ H := by
    intro x hx
    rw [hU] at hx ⊢
    induction hx using Subgroup.closure_induction with
    | mem y hy =>
        rw [Set.mem_iUnion₂] at hy
        obtain ⟨t, ht, k, rfl⟩ := hy
        rw [← mconj_pred]
        exact Subgroup.subset_closure (Set.mem_biUnion ht ⟨k - 1, rfl⟩)
    | one => simp
    | mul y z _ _ ihy ihz =>
        have hyz : β⁻¹ * (y * z) * β = (β⁻¹ * y * β) * (β⁻¹ * z * β) := by group
        rw [hyz]; exact Subgroup.mul_mem _ ihy ihz
    | inv y _ ihy =>
        have hy' : β⁻¹ * y⁻¹ * β = (β⁻¹ * y * β)⁻¹ := by group
        rw [hy']; exact Subgroup.inv_mem _ ihy
  have hconj := zpow_conj_mem hup hdown
  -- `H` together with `β` generates the whole group
  have htop : Subgroup.closure ((H : Set B) ∪ {β}) = ⊤ := by
    refine eq_top_iff.mpr ?_
    rw [← hS, Subgroup.closure_le]
    intro s hs
    rw [hs_eq s]
    refine Subgroup.mul_mem _ ?_ (Subgroup.zpow_mem _ (Subgroup.subset_closure (by simp)) _)
    refine Subgroup.subset_closure (Or.inl ?_)
    have := hgen s (Finset.mem_coe.mp hs) 0
    simpa using this
  -- every element of the group is an element of `H` times a power of `β`
  have hform : ∀ g : B, ∃ x ∈ H, ∃ k : ℤ, g = x * β ^ k := by
    intro g
    have hg : g ∈ Subgroup.closure ((H : Set B) ∪ {β}) := by rw [htop]; trivial
    induction hg using Subgroup.closure_induction with
    | mem y hy =>
        rcases hy with hy | hy
        · exact ⟨y, hy, 0, by simp⟩
        · rw [Set.mem_singleton_iff] at hy
          exact ⟨1, Subgroup.one_mem _, 1, by simp [hy]⟩
    | one => exact ⟨1, Subgroup.one_mem _, 0, by simp⟩
    | mul y z _ _ ihy ihz =>
        obtain ⟨x₁, hx₁, k₁, rfl⟩ := ihy
        obtain ⟨x₂, hx₂, k₂, rfl⟩ := ihz
        refine ⟨x₁ * (β ^ k₁ * x₂ * (β ^ k₁)⁻¹), Subgroup.mul_mem _ hx₁ (hconj k₁ x₂ hx₂),
          k₁ + k₂, ?_⟩
        rw [zpow_add]
        group
    | inv y _ ihy =>
        obtain ⟨x, hx, k, rfl⟩ := ihy
        refine ⟨β ^ (-k) * x⁻¹ * (β ^ (-k))⁻¹, hconj (-k) x⁻¹ (Subgroup.inv_mem _ hx), -k, ?_⟩
        group
  -- hence the kernel is exactly `H`
  have hker : φ.ker = H := by
    refine le_antisymm ?_ hHker
    intro g hg
    obtain ⟨x, hx, k, rfl⟩ := hform g
    have h1 : φ (β ^ k) = 1 := by
      have hx1 : φ x = 1 := MonoidHom.mem_ker.mp (hHker hx)
      have := MonoidHom.mem_ker.mp hg
      rw [map_mul, hx1, one_mul] at this
      exact this
    rw [hpow k] at h1
    have hk : k = 0 := by
      have := congrArg Multiplicative.toAdd h1
      simpa using this
    rw [hk]
    simpa using hx
  rw [Group.fg_iff_subgroup_fg, hker]
  exact ⟨U, rfl⟩

end Cyclic

/-! ### Normal series with cyclic quotients

The definitions and the four transport lemmas of this section are those of the published
`MilnorWolf.Lib` bundle (`IsCyclicStep`, `normal_isCyclic_comap`, `IsCyclicStep.comap`,
`IsCyclicStep.map`, `exists_chain_of_isPolycyclic`), repeated here so that this file stands on
its own, together with one new transport: a step of a normal series restricts to any subgroup
containing it. -/

section Series

open Function

/-- One step `H ⊆ K` of a normal series: `H ≤ K`, `H` is normal in `K`, and `K/H` is cyclic. -/
def IsCyclicStep {G : Type*} [Group G] (H K : Subgroup G) : Prop :=
  H ≤ K ∧ ∃ _ : (H.subgroupOf K).Normal, IsCyclic (K ⧸ H.subgroupOf K)

/-- Transport of "normal with cyclic quotient" along a surjection, by pulling the subgroup back. -/
theorem normal_isCyclic_comap {A B : Type*} [Group A] [Group B] (φ : A →* B)
    (hφ : Surjective φ) {Q : Subgroup B} (hn : Q.Normal) (hc : IsCyclic (B ⧸ Q)) :
    ∃ _ : (Q.comap φ).Normal, IsCyclic (A ⧸ Q.comap φ) := by
  have : Q.Normal := hn
  have hn' : (Q.comap φ).Normal := hn.comap φ
  refine ⟨hn', ?_⟩
  have hker : Q.comap φ = ((QuotientGroup.mk' Q).comp φ).ker := by
    rw [← MonoidHom.comap_ker, QuotientGroup.ker_mk']
  have hs : Surjective ((QuotientGroup.mk' Q).comp φ) :=
    (QuotientGroup.mk'_surjective Q).comp hφ
  have e : A ⧸ Q.comap φ ≃* B ⧸ Q :=
    (QuotientGroup.quotientMulEquivOfEq hker).trans
      (QuotientGroup.quotientKerEquivOfSurjective _ hs)
  exact isCyclic_of_surjective e.symm e.symm.surjective

/-- The restriction of `f : G →* H` to the preimage of `K`. -/
def restrictComap {G H : Type*} [Group G] [Group H] (f : G →* H) (K : Subgroup H) :
    ↥(K.comap f) →* ↥K :=
  (f.comp (K.comap f).subtype).codRestrict K (fun x => Subgroup.mem_comap.mp x.2)

theorem restrictComap_surjective {G H : Type*} [Group G] [Group H] {f : G →* H}
    (hf : Surjective f) (K : Subgroup H) : Surjective (restrictComap f K) := by
  rintro ⟨y, hy⟩
  obtain ⟨x, rfl⟩ := hf y
  exact ⟨⟨x, by simpa using hy⟩, rfl⟩

/-- A step of a normal series pulls back along a surjection. -/
theorem IsCyclicStep.comap {G H : Type*} [Group G] [Group H] {f : G →* H} (hf : Surjective f)
    {K₂ K₁ : Subgroup H} (h : IsCyclicStep K₂ K₁) :
    IsCyclicStep (K₂.comap f) (K₁.comap f) := by
  obtain ⟨hle, hnorm, hcyc⟩ := h
  refine ⟨Subgroup.comap_mono hle, ?_⟩
  have hkey : (K₂.subgroupOf K₁).comap (restrictComap f K₁) =
      (K₂.comap f).subgroupOf (K₁.comap f) := by
    ext x
    simp [Subgroup.mem_subgroupOf, restrictComap]
  have := normal_isCyclic_comap (restrictComap f K₁) (restrictComap_surjective hf K₁)
    hnorm hcyc
  rwa [hkey] at this

/-- A step of a normal series pushes forward along an injection. -/
theorem IsCyclicStep.map {G H : Type*} [Group G] [Group H] {f : G →* H} (hf : Injective f)
    {H₂ H₁ : Subgroup G} (h : IsCyclicStep H₂ H₁) :
    IsCyclicStep (H₂.map f) (H₁.map f) := by
  obtain ⟨hle, hnorm, hcyc⟩ := h
  refine ⟨Subgroup.map_mono hle, ?_⟩
  have hcoe : ∀ x : ↥(H₁.map f),
      f (((Subgroup.equivMapOfInjective H₁ f hf).symm x : ↥H₁) : G) = (x : H) := by
    intro x
    conv_rhs => rw [← MulEquiv.apply_symm_apply (Subgroup.equivMapOfInjective H₁ f hf) x]
    exact (Subgroup.coe_equivMapOfInjective_apply H₁ f hf _).symm
  have hkey : (H₂.subgroupOf H₁).comap
      ((Subgroup.equivMapOfInjective H₁ f hf).symm : ↥(H₁.map f) →* ↥H₁) =
      (H₂.map f).subgroupOf (H₁.map f) := by
    ext x
    simp only [Subgroup.mem_comap, Subgroup.mem_subgroupOf]
    rw [← hcoe x]
    exact (Subgroup.mem_map_iff_mem hf).symm
  have := normal_isCyclic_comap
    ((Subgroup.equivMapOfInjective H₁ f hf).symm : ↥(H₁.map f) →* ↥H₁)
    (Subgroup.equivMapOfInjective H₁ f hf).symm.surjective hnorm hcyc
  rwa [hkey] at this

theorem IsCyclicStep.congr {G : Type*} [Group G] {H K H' K' : Subgroup G} (h : IsCyclicStep H K)
    (e₁ : H = H') (e₂ : K = K') : IsCyclicStep H' K' := e₁ ▸ e₂ ▸ h

/-- The trivial step `⊥ ⊆ ⊥`. -/
theorem isCyclicStep_of_eq_bot {G : Type*} [Group G] {H K : Subgroup G} (hH : H = ⊥)
    (hK : K = ⊥) : IsCyclicStep H K := by
  subst hH; subst hK
  have hn : ((⊥ : Subgroup G).subgroupOf ⊥).Normal := by
    rw [Subgroup.subgroupOf_bot_eq_top]; infer_instance
  exact ⟨le_rfl, hn,
    isCyclic_of_surjective (QuotientGroup.mk' _) (QuotientGroup.mk'_surjective _)⟩

/-- **A step of a normal series restricts to a larger subgroup.**  If `H ⊆ K` is a step and
`K ≤ L`, then `H ∩ L ⊆ K ∩ L` is a step of a normal series of `L`; this is what lets the
induction descend into the group `L` while keeping the rest of the series. -/
theorem IsCyclicStep.subgroupOf {G : Type*} [Group G] {H K L : Subgroup G}
    (h : IsCyclicStep H K) (hKL : K ≤ L) :
    IsCyclicStep (H.subgroupOf L) (K.subgroupOf L) := by
  obtain ⟨hle, hnorm, hcyc⟩ := h
  refine ⟨fun x hx => hle hx, ?_⟩
  have hkey : (H.subgroupOf K).comap
      ((Subgroup.subgroupOfEquivOfLe hKL : ↥(K.subgroupOf L) ≃* ↥K) : ↥(K.subgroupOf L) →* ↥K)
      = (H.subgroupOf L).subgroupOf (K.subgroupOf L) := by
    ext x
    simp [Subgroup.mem_subgroupOf, Subgroup.subgroupOfEquivOfLe]
  have := normal_isCyclic_comap
    ((Subgroup.subgroupOfEquivOfLe hKL : ↥(K.subgroupOf L) ≃* ↥K) : ↥(K.subgroupOf L) →* ↥K)
    (Subgroup.subgroupOfEquivOfLe hKL).surjective hnorm hcyc
  rwa [hkey] at this

/-- The terms of a normal series decrease. -/
theorem chain_le {G : Type*} [Group G] {D : ℕ → Subgroup G}
    (hstep : ∀ i, IsCyclicStep (D (i + 1)) (D i)) : ∀ i j, i ≤ j → D j ≤ D i := by
  intro i j
  induction j with
  | zero =>
      intro hij
      have : i = 0 := by omega
      subst this
      exact le_rfl
  | succ n ih =>
      intro hij
      rcases Nat.lt_or_ge i (n + 1) with hlt | hge
      · exact le_trans (hstep n).1 (ih (by omega))
      · have : i = n + 1 := by omega
        subst this
        exact le_rfl

/-- A polycyclic group has an `ℕ`-indexed normal series with cyclic quotients. -/
theorem exists_chain_of_isPolycyclic {G : Type*} [Group G] (h : MilnorWolf.IsPolycyclic G) :
    ∃ (A : ℕ → Subgroup G) (t : ℕ), A 0 = ⊤ ∧ A t = ⊥ ∧
      ∀ i, IsCyclicStep (A (i + 1)) (A i) := by
  obtain ⟨t, A, h0, hlast, hstep⟩ := h
  have hbot : ∀ m, t ≤ m →
      A ⟨min m t, Nat.lt_succ_of_le (min_le_right m t)⟩ = ⊥ := by
    intro m hm
    rw [← hlast]
    exact congrArg A (Fin.ext (by simp [Fin.val_last]; omega))
  refine ⟨fun n => A ⟨min n t, Nat.lt_succ_of_le (min_le_right n t)⟩, t, ?_, ?_, ?_⟩
  · rw [← h0]; exact congrArg A (Fin.ext (by simp))
  · exact hbot t le_rfl
  · intro i
    rcases lt_or_ge i t with hi | hi
    · refine IsCyclicStep.congr (hstep ⟨i, hi⟩) (congrArg A (Fin.ext ?_))
        (congrArg A (Fin.ext ?_))
      · simp only [Fin.val_succ]; omega
      · simp only [Fin.val_castSucc]; omega
    · exact isCyclicStep_of_eq_bot (hbot (i + 1) (by omega)) (hbot i hi)

end Series

/-! ### Two transfers -/

section Transfer

/-- Finite generation transfers along an isomorphism. -/
theorem fg_of_mulEquiv {A B : Type*} [Group A] [Group B] (e : A ≃* B) (h : Group.FG A) :
    Group.FG B := by
  classical
  obtain ⟨S, hS⟩ := h.out
  exact ⟨⟨S.image (e : A →* B), by
    rw [Finset.coe_image, ← MonoidHom.map_closure, hS, ← MonoidHom.range_eq_map,
      MonoidHom.range_eq_top]
    exact e.surjective⟩⟩

/-- Having no free subsemigroup on two generators passes to subgroups: a free subsemigroup of a
subgroup is one of the group. -/
theorem not_hasFreeSubsemigroupOfRankTwo_subgroup {G : Type*} [Group G]
    (h : ¬ HasFreeSubsemigroupOfRankTwo G) (H : Subgroup G) :
    ¬ HasFreeSubsemigroupOfRankTwo ↥H := by
  rintro ⟨a, b, hinj⟩
  refine h ⟨(a : G), (b : G), ?_⟩
  have hcomp : FreeMonoid.lift ![(a : G), (b : G)]
      = (H.subtype).comp (FreeMonoid.lift ![a, b]) := by
    refine FreeMonoid.hom_eq ?_
    intro x
    fin_cases x <;> simp
  rw [hcomp, MonoidHom.coe_comp]
  exact (Subgroup.subtype_injective H).comp hinj

/-- An infinite cyclic group is `ℤ`. -/
theorem nonempty_mulEquiv_int (Q : Type*) [Group Q] [IsCyclic Q] [Infinite Q] :
    Nonempty (Q ≃* Multiplicative ℤ) := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Q)
  have hfo : ¬ IsOfFinOrder g := by
    intro hfin
    have hfinite : (Subgroup.zpowers g : Set Q).Finite := finite_zpowers.mpr hfin
    have huniv : (Subgroup.zpowers g : Set Q) = Set.univ := by
      ext x
      simp [hg x]
    rw [huniv] at hfinite
    exact (Set.infinite_univ (α := Q)) hfinite
  have hzinj : Function.Injective (fun n : ℤ => g ^ n) :=
    injective_zpow_iff_not_isOfFinOrder.mpr hfo
  have hinj : Function.Injective (zpowersHom Q g) := by
    intro m n hmn
    rw [zpowersHom_apply, zpowersHom_apply] at hmn
    exact Multiplicative.toAdd.injective (hzinj hmn)
  have hsurj : Function.Surjective (zpowersHom Q g) := by
    intro x
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hg x)
    exact ⟨Multiplicative.ofAdd k, by rw [zpowersHom_apply]; simpa using hk⟩
  exact ⟨(MulEquiv.ofBijective _ ⟨hinj, hsurj⟩ : Multiplicative ℤ ≃* Q).symm⟩

end Transfer

/-! ### The induction along the series -/

/-- The engine of the assembly: if a finitely generated group with no free subsemigroup on two
generators has a normal series with cyclic quotients starting at a subgroup of finite index, then
every term of the series is finitely generated.

The induction is on the length of the series.  A finite cyclic step keeps the ambient group and
shortens the series, the new head still having finite index (Schreier); an infinite cyclic step
is a surjection of `D 0` onto `ℤ`, so its kernel `D 1` is finitely generated by Milnor's Lemma 1
in the form supplied by Rosenblatt's Lemma 4.8, and the induction continues inside `D 1`, where
the head of the shortened series is everything.  This is where Rosenblatt's own assembly (4.10,
p. 44) instead builds a tower of conjugates, whose finiteness needs `A` abelian. -/
theorem fg_of_chain : ∀ (t : ℕ) (G : Type u) [Group G] [Group.FG G],
    ¬ HasFreeSubsemigroupOfRankTwo G → ∀ D : ℕ → Subgroup G, (D 0).index ≠ 0 →
    (∀ i, IsCyclicStep (D (i + 1)) (D i)) → Group.FG (D t) := by
  intro t
  induction t with
  | zero =>
      intro G _ _ _ D hD0 _
      have : (D 0).FiniteIndex := ⟨hD0⟩
      exact Subgroup.fg_of_index_ne_zero (D 0)
  | succ t ih =>
      intro G _ _ hfree D hD0 hstep
      have : (D 0).FiniteIndex := ⟨hD0⟩
      obtain ⟨hle, hnorm, hcyc⟩ := hstep 0
      have := hnorm
      have := hcyc
      by_cases hfin : Finite (↥(D 0) ⧸ (D 1).subgroupOf (D 0))
      · -- a finite cyclic step: `D 1` still has finite index in `G`
        have := hfin
        have hrel : (D 1).relIndex (D 0) ≠ 0 := Subgroup.index_ne_zero_of_finite
        have hD1 : (D 1).index ≠ 0 := by
          rw [← Subgroup.relIndex_mul_index hle]
          exact Nat.mul_ne_zero hrel hD0
        exact ih G hfree (fun i => D (i + 1)) hD1 (fun i => hstep (i + 1))
      · -- an infinite cyclic step: a surjection of `D 0` onto `ℤ`
        have : Infinite (↥(D 0) ⧸ (D 1).subgroupOf (D 0)) := not_finite_iff_infinite.mp hfin
        have hFG0 : Group.FG ↥(D 0) := Subgroup.fg_of_index_ne_zero (D 0)
        have := hFG0
        have hfree0 : ¬ HasFreeSubsemigroupOfRankTwo ↥(D 0) :=
          not_hasFreeSubsemigroupOfRankTwo_subgroup hfree _
        obtain ⟨e⟩ := nonempty_mulEquiv_int (↥(D 0) ⧸ (D 1).subgroupOf (D 0))
        set φ : ↥(D 0) →* Multiplicative ℤ :=
          (e : (↥(D 0) ⧸ (D 1).subgroupOf (D 0)) →* Multiplicative ℤ).comp
            (QuotientGroup.mk' ((D 1).subgroupOf (D 0))) with hφdef
        have hsurj : Function.Surjective φ :=
          e.surjective.comp (QuotientGroup.mk'_surjective _)
        have hkerφ : φ.ker = (D 1).subgroupOf (D 0) := by
          have he : (e : (↥(D 0) ⧸ (D 1).subgroupOf (D 0)) →* Multiplicative ℤ).ker = ⊥ :=
            (MonoidHom.ker_eq_bot_iff _).mpr e.injective
          rw [hφdef, ← MonoidHom.comap_ker, he, MonoidHom.comap_bot, QuotientGroup.ker_mk']
        have hfgker : Group.FG ↥(φ.ker) := fg_ker_of_surjective_int hfree0 φ hsurj
        rw [hkerφ] at hfgker
        have hfg1 : Group.FG ↥(D 1) :=
          fg_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hle) hfgker
        have := hfg1
        have hmono := chain_le hstep
        have hD1le : ∀ i, D (i + 1) ≤ D 1 := fun i => hmono 1 (i + 1) (by omega)
        have hfree1 : ¬ HasFreeSubsemigroupOfRankTwo ↥(D 1) :=
          not_hasFreeSubsemigroupOfRankTwo_subgroup hfree _
        have hhead : (((D 1).subgroupOf (D 1)) : Subgroup ↥(D 1)).index ≠ 0 := by
          rw [Subgroup.subgroupOf_self, Subgroup.index_top]
          exact one_ne_zero
        have key := ih ↥(D 1) hfree1 (fun i => (D (i + 1)).subgroupOf (D 1)) hhead
          (fun i => (hstep (i + 1)).subgroupOf (hD1le i))
        exact fg_of_mulEquiv (Subgroup.subgroupOfEquivOfLe (hD1le t)) key

end Rbt

/-! ### Rosenblatt's Lemmas 4.8–4.10 in the form Chou's Theorem 3.2′ uses them -/

namespace Lib

open Chou Chou.Rbt

/-- **Rosenblatt's Lemmas 4.8 and 4.9** (Trans. Amer. Math. Soc. 193 (1974), pp. 42–43) in the
form Chou's proof of Theorem 3.2′ uses them (p. 401, "with the understanding that `A` doesn't
have to be abelian there"): in a finitely generated group with no free subsemigroup on two
generators, a normal subgroup whose quotient is virtually polycyclic is finitely generated. -/
theorem fg_of_isVirtuallyPolycyclic_quotient_of_not_hasFreeSubsemigroupOfRankTwo' {G : Type*}
    [Group G] [Group.FG G] (hfree : ¬ HasFreeSubsemigroupOfRankTwo G) (N : Subgroup G) [N.Normal]
    (hq : ∃ H : Subgroup (G ⧸ N), H.FiniteIndex ∧ MilnorWolf.IsPolycyclic H) :
    Group.FG N := by
  obtain ⟨H, hFI, hpoly⟩ := hq
  obtain ⟨A, t, hA0, hAt, hAstep⟩ := exists_chain_of_isPolycyclic hpoly
  -- the series of `H`, read in `G ⧸ N`
  have hB0 : (A 0).map H.subtype = H := by
    rw [hA0, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have hBt : (A t).map H.subtype = ⊥ := by
    rw [hAt, Subgroup.map_bot]
  have hBstep : ∀ i, IsCyclicStep ((A (i + 1)).map H.subtype) ((A i).map H.subtype) :=
    fun i => (hAstep i).map (Subgroup.subtype_injective H)
  -- and pulled back to `G`, where it ends at `N`
  set D : ℕ → Subgroup G :=
    fun i => ((A i).map H.subtype).comap (QuotientGroup.mk' N) with hD
  have hD0 : (D 0).index ≠ 0 := by
    rw [hD]
    simp only
    rw [hB0, Subgroup.index_comap_of_surjective _ (QuotientGroup.mk'_surjective N)]
    exact Subgroup.finiteIndex_iff.mp hFI
  have hDt : D t = N := by
    rw [hD]
    simp only
    rw [hBt, MonoidHom.comap_bot, QuotientGroup.ker_mk']
  have hDstep : ∀ i, IsCyclicStep (D (i + 1)) (D i) :=
    fun i => (hBstep i).comap (QuotientGroup.mk'_surjective N)
  have := fg_of_chain t G hfree D hD0 hDstep
  rwa [hDt] at this

end Lib

end Chou

open Chou

theorem solution {G : Type*}
    [Group G] [Group.FG G] (hfree : ¬ HasFreeSubsemigroupOfRankTwo G) (N : Subgroup G) [N.Normal]
    (hq : ∃ H : Subgroup (G ⧸ N), H.FiniteIndex ∧ MilnorWolf.IsPolycyclic H) :
    Group.FG N :=
  Chou.Lib.fg_of_isVirtuallyPolycyclic_quotient_of_not_hasFreeSubsemigroupOfRankTwo' hfree N hq
