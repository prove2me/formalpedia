-- Prove2me | solution 1 for DiscreteConvex.MConvexSets.mconvex_set_iff_base_polyhedron
-- status  : ACCEPTED   (prove)
-- author  : @Tim
-- created : 2026-10-05T18:06:58.182719+00:00
-- url     : https://prove2.me/submissions/421e3038-f6b0-4a05-ade9-060c7224ed52

import Mathlib
import Definitions.Def_DiscreteConvex_MConvexSets_ExchangeAxiomB
import Definitions.Def_DiscreteConvex_MConvexSets_SubmodularSetFunction
import Definitions.Def_DiscreteConvex_MConvexSets_BasePolyhedron
import Definitions.Def_DiscreteConvex_MConvexSets_IsIntegerValued

open DiscreteConvex.MConvexSets

namespace MConvBase

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The `ℓ₁` distance of two integer vectors, used as the induction measure. -/
def l1 (x y : V → ℤ) : ℕ := ∑ w, (x w - y w).natAbs


lemma mem_of_eq {B : Set (V → ℤ)} {f g : V → ℤ} (hf : f ∈ B) (h : ∀ t, f t = g t) : g ∈ B :=
  funext h ▸ hf

lemma l1_y_step (x y : V → ℤ) (a b : V) (ha : x a < y a) (hb : y b < x b) :
    l1 x (fun w => y w - CharVec a w + CharVec b w) < l1 x y := by
  have hab : a ≠ b := fun h => by subst h; omega
  apply Finset.sum_lt_sum
  · intro w _
    simp only [CharVec]
    split_ifs <;> subst_vars <;> first | omega | simp_all
  · refine ⟨b, Finset.mem_univ _, ?_⟩
    simp only [CharVec, if_neg hab.symm, eq_self_iff_true, if_true]
    omega

lemma l1_x_step (x y : V → ℤ) (a b : V) (ha : x a < y a) (hb : y b < x b) :
    l1 (fun w => x w + CharVec a w - CharVec b w) y < l1 x y := by
  have hab : a ≠ b := fun h => by subst h; omega
  apply Finset.sum_lt_sum
  · intro w _
    simp only [CharVec]
    split_ifs <;> subst_vars <;> first | omega | simp_all
  · refine ⟨b, Finset.mem_univ _, ?_⟩
    simp only [CharVec, if_neg hab.symm, eq_self_iff_true, if_true]
    omega

/-- `x(X) = ∑_{v ∈ X} x(v)` for an integer vector. -/
def sig (z : V → ℤ) (X : Finset V) : ℤ := ∑ v ∈ X, z v

lemma sum_cv (X : Finset V) (u : V) : ∑ v ∈ X, CharVec u v = if u ∈ X then 1 else 0 := by
  simp [CharVec]

lemma sig_mod (z : V → ℤ) (a b : V) (X : Finset V) :
    sig (fun w => z w - CharVec a w + CharVec b w) X =
      sig z X - (if a ∈ X then 1 else 0) + (if b ∈ X then 1 else 0) := by
  simp only [sig, Finset.sum_add_distrib, Finset.sum_sub_distrib, sum_cv]

lemma sig_union_inter (z : V → ℤ) (X Y : Finset V) :
    sig z (X ∪ Y) + sig z (X ∩ Y) = sig z X + sig z Y := by
  simp only [sig]; exact Finset.sum_union_inter

lemma memBP_iff (ρ : Finset V → WithTop ℝ) (z : V → ℤ) :
    (fun v => (z v : ℝ)) ∈ BasePolyhedron ρ ↔
      (∀ X, (((sig z X : ℤ) : ℝ) : WithTop ℝ) ≤ ρ X) ∧
        (((sig z Finset.univ : ℤ) : ℝ) : WithTop ℝ) = ρ Finset.univ := by
  unfold BasePolyhedron
  simp only [Set.mem_ofPred_eq, sig, Int.cast_sum]

/-! ### From an M-convex set to a submodular function -/

section forward

variable {B : Set (V → ℤ)}

/-- All points of an M-convex set have the same coordinate sum. -/
lemma sum_eq (hB : ExchangeAxiomB B) : ∀ x ∈ B, ∀ y ∈ B, sig x Finset.univ = sig y Finset.univ := by
  suffices H : ∀ n, ∀ x ∈ B, ∀ y ∈ B, l1 x y = n → sig x Finset.univ = sig y Finset.univ from
    fun x hx y hy => H _ x hx y hy rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro x hx y hy hn
  by_cases h : ∃ u, y u < x u
  · obtain ⟨u, hu⟩ := h
    obtain ⟨v, hv, -, hyv⟩ := hB x hx y hy u hu
    have hv' : x v < y v := hv
    have hy' : (fun w => y w - CharVec v w + CharVec u w) ∈ B :=
      mem_of_eq hyv fun t => by ring
    rw [ih _ (hn ▸ l1_y_step x y v u hv' hu) x hx _ hy' rfl, sig_mod]
    simp
  · push_neg at h
    by_cases h2 : ∃ w, x w < y w
    · obtain ⟨w, hw⟩ := h2
      obtain ⟨v, hv, -⟩ := hB y hy x hx w hw
      have hv' : y v < x v := hv
      exact absurd (h v) (not_le.2 hv')
    · push_neg at h2
      have : x = y := funext fun w => le_antisymm (h w) (h2 w)
      rw [this]

/-- For nested `A ⊆ C` and `a, c ∈ B` there is `z ∈ B` with `z(A) ≥ a(A)` and `z(C) ≥ c(C)`. -/
lemma chain (hB : ExchangeAxiomB B) (A C : Finset V) (hAC : A ⊆ C) :
    ∀ n, ∀ a ∈ B, ∀ c ∈ B, l1 a c = n → ∃ z ∈ B, sig a A ≤ sig z A ∧ sig c C ≤ sig z C := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro a ha c hc hn
  by_cases hle : sig a A ≤ sig c A
  · exact ⟨c, hc, hle, le_rfl⟩
  push_neg at hle
  obtain ⟨u, huA, hu⟩ := Finset.exists_lt_of_sum_lt hle
  obtain ⟨v, hv, -, hcv⟩ := hB a ha c hc u hu
  have hv' : a v < c v := hv
  have hc' : (fun w => c w - CharVec v w + CharVec u w) ∈ B :=
    mem_of_eq hcv fun t => by ring
  obtain ⟨z, hz, h1, h2⟩ := ih _ (hn ▸ l1_y_step a c v u hv' hu) a ha _ hc' rfl
  refine ⟨z, hz, h1, le_trans ?_ h2⟩
  rw [sig_mod, if_pos (hAC huA)]
  split_ifs <;> omega

/-- The set of values `x(X)`, `x ∈ B`. -/
def S (B : Set (V → ℤ)) (X : Finset V) : Set ℤ := (fun x => sig x X) '' B

open Classical in
/-- `ρ(X) = sup_{x ∈ B} x(X)` (Eq. (4.25)), `+∞` when unbounded. -/
noncomputable def rho (B : Set (V → ℤ)) (X : Finset V) : WithTop ℝ :=
  if BddAbove (S B X) then (((sSup (S B X) : ℤ) : ℝ) : WithTop ℝ) else ⊤

lemma rho_of_bdd {X : Finset V} (h : BddAbove (S B X)) :
    rho B X = (((sSup (S B X) : ℤ) : ℝ) : WithTop ℝ) := by
  unfold rho; rw [if_pos h]

lemma rho_of_not_bdd {X : Finset V} (h : ¬BddAbove (S B X)) : rho B X = ⊤ := by
  unfold rho; rw [if_neg h]

lemma le_sup {X : Finset V} {x : V → ℤ} (hx : x ∈ B) (h : BddAbove (S B X)) :
    sig x X ≤ sSup (S B X) :=
  le_csSup h ⟨x, hx, rfl⟩

lemma attain {X : Finset V} (hne : B.Nonempty) (h : BddAbove (S B X)) :
    ∃ x ∈ B, sig x X = sSup (S B X) := by
  obtain ⟨x, hx, hxe⟩ := Int.csSup_mem (hne.image _) h
  exact ⟨x, hx, hxe⟩

lemma rho_submod (hB : ExchangeAxiomB B) (hne : B.Nonempty) (X Y : Finset V) :
    rho B X + rho B Y ≥ rho B (X ∪ Y) + rho B (X ∩ Y) := by
  by_cases hX : BddAbove (S B X)
  swap
  · rw [rho_of_not_bdd hX, WithTop.top_add]; exact le_top
  by_cases hY : BddAbove (S B Y)
  swap
  · rw [rho_of_not_bdd hY, WithTop.add_top]; exact le_top
  obtain ⟨a0, ha0⟩ := hne
  have key : ∀ a ∈ B, ∀ c ∈ B,
      sig a (X ∩ Y) + sig c (X ∪ Y) ≤ sSup (S B X) + sSup (S B Y) := by
    intro a ha c hc
    obtain ⟨z, hz, h1, h2⟩ :=
      chain hB (X ∩ Y) (X ∪ Y) Finset.inter_subset_union _ a ha c hc rfl
    have h3 := le_sup hz hX
    have h4 := le_sup hz hY
    have e := sig_union_inter z X Y
    linarith
  have hU : BddAbove (S B (X ∪ Y)) := ⟨sSup (S B X) + sSup (S B Y) - sig a0 (X ∩ Y), by
    rintro _ ⟨c, hc, rfl⟩
    have := key a0 ha0 c hc
    linarith⟩
  have hI : BddAbove (S B (X ∩ Y)) := ⟨sSup (S B X) + sSup (S B Y) - sig a0 (X ∪ Y), by
    rintro _ ⟨a, ha, rfl⟩
    have := key a ha a0 ha0
    linarith⟩
  obtain ⟨c, hc, hce⟩ := attain ⟨a0, ha0⟩ hU
  obtain ⟨a, ha, hae⟩ := attain ⟨a0, ha0⟩ hI
  have := key a ha c hc
  rw [rho_of_bdd hX, rho_of_bdd hY, rho_of_bdd hU, rho_of_bdd hI, ge_iff_le,
    ← WithTop.coe_add, ← WithTop.coe_add, WithTop.coe_le_coe, ← hce, ← hae]
  exact_mod_cast (by linarith : sig c (X ∪ Y) + sig a (X ∩ Y) ≤ sSup (S B X) + sSup (S B Y))

lemma bdd_univ (hB : ExchangeAxiomB B) {b : V → ℤ} (hb : b ∈ B) :
    BddAbove (S B Finset.univ) :=
  ⟨sig b Finset.univ, by rintro _ ⟨y, hy, rfl⟩; exact le_of_eq (sum_eq hB y hy b hb)⟩

lemma rho_univ (hB : ExchangeAxiomB B) {b : V → ℤ} (hb : b ∈ B) :
    rho B Finset.univ = (((sig b Finset.univ : ℤ) : ℝ) : WithTop ℝ) := by
  have hbu := bdd_univ hB hb
  obtain ⟨z, hz, hze⟩ := attain ⟨b, hb⟩ hbu
  rw [rho_of_bdd hbu, ← hze, sum_eq hB z hz b hb]

lemma rho_props (hB : ExchangeAxiomB B) (hne : B.Nonempty) :
    SubmodularSetFunction (rho B) ∧ IsIntegerValued (rho B) := by
  obtain ⟨b, hb⟩ := hne
  refine ⟨⟨?_, ?_, rho_submod hB ⟨b, hb⟩⟩, ?_⟩
  · have h0 : BddAbove (S B ∅) := ⟨0, by rintro _ ⟨x, -, rfl⟩; simp [sig]⟩
    obtain ⟨z, -, hze⟩ := attain ⟨b, hb⟩ h0
    rw [rho_of_bdd h0, ← hze]
    simp [sig]
  · rw [rho_univ hB hb]; exact WithTop.coe_ne_top
  · intro X
    by_cases h : BddAbove (S B X)
    · exact Or.inr ⟨_, rho_of_bdd h⟩
    · exact Or.inl (rho_of_not_bdd h)

lemma subset_bp (hB : ExchangeAxiomB B) {x : V → ℤ} (hx : x ∈ B) :
    (fun v => (x v : ℝ)) ∈ BasePolyhedron (rho B) := by
  rw [memBP_iff]
  refine ⟨fun X => ?_, (rho_univ hB hx).symm⟩
  by_cases h : BddAbove (S B X)
  · rw [rho_of_bdd h, WithTop.coe_le_coe]
    exact_mod_cast le_sup hx h
  · rw [rho_of_not_bdd h]; exact le_top

/-- Every integer point of `B(ρ)` lies in `B`. -/
lemma bp_subset (hB : ExchangeAxiomB B) (hne : B.Nonempty) (x : V → ℤ)
    (hx : (fun v => (x v : ℝ)) ∈ BasePolyhedron (rho B)) : x ∈ B := by
  rw [memBP_iff] at hx
  obtain ⟨hxX, hxV⟩ := hx
  obtain ⟨b0, hb0⟩ := hne
  suffices H : ∀ n, ∀ b ∈ B, l1 x b = n → x ∈ B from H _ b0 hb0 rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro b hb hn
  by_cases hcl : ∃ b' ∈ B, l1 x b' < l1 x b
  · obtain ⟨b', hb', hlt⟩ := hcl
    exact ih _ (hn ▸ hlt) b' hb' rfl
  push_neg at hcl
  have hbV : sig b Finset.univ = sig x Finset.univ := by
    rw [rho_univ hB hb, WithTop.coe_eq_coe] at hxV
    exact_mod_cast hxV.symm
  by_cases hu : ∃ u, b u < x u
  swap
  · push_neg at hu
    have hxb : x = b := by
      funext w
      exact (Finset.sum_eq_sum_iff_of_le (fun i _ => hu i)).1 (by simpa [sig] using hbV.symm) w
        (Finset.mem_univ _)
    exact hxb ▸ hb
  obtain ⟨u, hu⟩ := hu
  classical
  let X : Finset V := Finset.univ.filter (fun w => (fun t => b t + CharVec u t - CharVec w t) ∈ B)
  have hmemX : ∀ w, w ∈ X ↔ (fun t => b t + CharVec u t - CharVec w t) ∈ B := by
    intro w; simp [X]
  have huX : u ∈ X := (hmemX u).2 (mem_of_eq hb fun t => by ring)
  -- every point of `B` has `y(X) ≤ b(X)`
  have claim : ∀ m, ∀ y ∈ B, l1 y b = m → sig y X ≤ sig b X := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ihm =>
    intro y hy hm
    by_contra hlt
    push_neg at hlt
    obtain ⟨p, hpX, hp⟩ := Finset.exists_lt_of_sum_lt hlt
    obtain ⟨q, hq, hyq, hbq⟩ := hB y hy b hb p hp
    have hq' : y q < b q := hq
    have hpq : p ≠ q := fun h => by subst h; omega
    have hqX : q ∈ X := by
      by_contra hqX
      by_cases hpu : p = u
      · subst hpu; exact hqX ((hmemX q).2 hbq)
      · have hb2 := (hmemX p).1 hpX
        have hqu : q ≠ u := fun h => hqX (h ▸ huX)
        obtain ⟨v, hv, h1, h2⟩ := hB _ hbq _ hb2 p (by
          simp only [SuppPos, Set.mem_ofPred_eq, CharVec, if_neg hpu, if_neg hpq,
            eq_self_iff_true, if_true]
          omega)
        have hv' := hv
        simp only [SuppNeg, Set.mem_ofPred_eq, CharVec] at hv'
        have hvqu : v = q ∨ v = u := by
          by_contra hne
          push_neg at hne
          rw [if_neg hne.1, if_neg hne.2] at hv'
          split_ifs at hv' <;> omega
        rcases hvqu with rfl | rfl
        · exact hqX ((hmemX v).2 (mem_of_eq h2 fun t => by (simp only [CharVec] <;> split_ifs <;> subst_vars <;> first | omega | simp_all)))
        · exact hqX ((hmemX q).2 (mem_of_eq h1 fun t => by (simp only [CharVec] <;> split_ifs <;> subst_vars <;> first | omega | simp_all)))
    have hy' : (fun w => y w + CharVec q w - CharVec p w) ∈ B :=
      mem_of_eq hyq fun t => by ring
    have hlt' := ihm _ (hm ▸ l1_x_step y b q p hq' hp) _ hy' rfl
    have e : sig (fun w => y w + CharVec q w - CharVec p w) X = sig y X := by
      have : (fun w => y w + CharVec q w - CharVec p w) = fun w => y w - CharVec p w + CharVec q w :=
        funext fun t => by ring
      rw [this, sig_mod, if_pos hpX, if_pos hqX]; ring
    omega
  have hbdd : BddAbove (S B X) := ⟨sig b X, by rintro _ ⟨y, hy, rfl⟩; exact claim _ y hy rfl⟩
  have hsup : sSup (S B X) ≤ sig b X :=
    csSup_le ⟨_, b, hb, rfl⟩ (by rintro _ ⟨y, hy, rfl⟩; exact claim _ y hy rfl)
  have hxle : sig x X ≤ sig b X := by
    have h := hxX X
    rw [rho_of_bdd hbdd, WithTop.coe_le_coe] at h
    have : sig x X ≤ sSup (S B X) := by exact_mod_cast h
    omega
  have hlt : sig b X < sig x X := by
    apply Finset.sum_lt_sum _ ⟨u, huX, hu.le.lt_of_ne (ne_of_lt hu)⟩
    intro w hw
    by_contra hwx
    push_neg at hwx
    have hwu : w ≠ u := fun h => by subst h; omega
    have hb' : (fun t => b t - CharVec w t + CharVec u t) ∈ B :=
      mem_of_eq ((hmemX w).1 hw) fun t => by ring
    exact absurd (hcl _ hb') (not_le.2 (l1_y_step x b w u hwx hu))
  omega

end forward

/-! ### From a submodular function to an M-convex set -/

section backward

variable (ρ : Finset V → WithTop ℝ)

/-- `z ∈ B(ρ) ∩ Zⱽ`. -/
def InB (z : V → ℤ) : Prop := (fun v => (z v : ℝ)) ∈ BasePolyhedron ρ

/-- `X` is tight for `z`: `z(X) = ρ(X)`. -/
def Tight (z : V → ℤ) (X : Finset V) : Prop := (((sig z X : ℤ) : ℝ) : WithTop ℝ) = ρ X

variable {ρ}

lemma tight_union_inter (hρ : SubmodularSetFunction ρ) {z : V → ℤ} (hz : InB ρ z)
    {X Y : Finset V} (hX : Tight ρ z X) (hY : Tight ρ z Y) :
    Tight ρ z (X ∪ Y) ∧ Tight ρ z (X ∩ Y) := by
  obtain ⟨hle, -⟩ := (memBP_iff ρ z).1 hz
  have hsub := hρ.2.2 X Y
  unfold Tight at *
  rw [← hX, ← hY, ← WithTop.coe_add] at hsub
  have hU := hle (X ∪ Y)
  have hI := hle (X ∩ Y)
  have hUt : ρ (X ∪ Y) ≠ ⊤ := fun h => by
    rw [h, WithTop.top_add] at hsub; exact WithTop.coe_ne_top (top_le_iff.1 hsub)
  have hIt : ρ (X ∩ Y) ≠ ⊤ := fun h => by
    rw [h, WithTop.add_top] at hsub; exact WithTop.coe_ne_top (top_le_iff.1 hsub)
  obtain ⟨r1, hr1⟩ := WithTop.ne_top_iff_exists.1 hUt
  obtain ⟨r2, hr2⟩ := WithTop.ne_top_iff_exists.1 hIt
  rw [← hr1] at hsub hU ⊢
  rw [← hr2] at hsub hI ⊢
  rw [← WithTop.coe_add, ge_iff_le, WithTop.coe_le_coe] at hsub
  rw [WithTop.coe_le_coe] at hU hI
  have e : ((sig z (X ∪ Y) : ℤ) : ℝ) + (sig z (X ∩ Y) : ℝ) = (sig z X : ℝ) + (sig z Y : ℝ) := by
    exact_mod_cast sig_union_inter z X Y
  constructor <;> rw [WithTop.coe_eq_coe] <;> linarith

lemma slack (hint : IsIntegerValued ρ) {z : V → ℤ} (hz : InB ρ z) (X : Finset V)
    (hnt : ¬Tight ρ z X) : (((sig z X + 1 : ℤ) : ℝ) : WithTop ℝ) ≤ ρ X := by
  rcases hint X with h | ⟨k, hk⟩
  · rw [h]; exact le_top
  · have h1 := ((memBP_iff ρ z).1 hz).1 X
    unfold Tight at hnt
    rw [hk] at h1 hnt ⊢
    rw [WithTop.coe_le_coe] at h1 ⊢
    rw [WithTop.coe_eq_coe] at hnt
    have h1' : sig z X ≤ k := by exact_mod_cast h1
    have h2 : sig z X ≠ k := fun h => hnt (by rw [h])
    exact_mod_cast (by omega : sig z X + 1 ≤ k)

/-- If every tight set of `z` containing `b` also contains `a`, then `z - χ_a + χ_b ∈ B(ρ)`. -/
lemma move (hint : IsIntegerValued ρ) {z : V → ℤ} (hz : InB ρ z) (a b : V)
    (h : ∀ X, Tight ρ z X → b ∈ X → a ∈ X) : InB ρ (fun w => z w - CharVec a w + CharVec b w) := by
  have hz' := (memBP_iff ρ z).1 hz
  unfold InB
  rw [memBP_iff]
  refine ⟨fun X => ?_, ?_⟩
  · rw [sig_mod]
    have mono : ∀ s : ℤ, s ≤ sig z X → (((s : ℤ) : ℝ) : WithTop ℝ) ≤ ρ X := fun s hs =>
      (WithTop.coe_le_coe.2 (Int.cast_le.2 hs)).trans (hz'.1 X)
    by_cases hbX : b ∈ X
    · by_cases haX : a ∈ X
      · rw [if_pos haX, if_pos hbX]; exact mono _ (by omega)
      · have hnt : ¬Tight ρ z X := fun ht => haX (h X ht hbX)
        rw [if_neg haX, if_pos hbX, sub_zero]; exact slack hint hz X hnt
    · split_ifs <;> exact mono _ (by omega)
  · rw [sig_mod, if_pos (Finset.mem_univ a), if_pos (Finset.mem_univ b), sub_add_cancel]
    exact hz'.2

theorem backward (hρ : SubmodularSetFunction ρ) (hint : IsIntegerValued ρ) :
    ExchangeAxiomB {x : V → ℤ | InB ρ x} := by
  intro x hx y hy u hu
  have hx : InB ρ x := hx
  have hy : InB ρ y := hy
  have hu' : y u < x u := hu
  classical
  -- `D`: a minimal tight set of `y` containing `u`
  let FD := (Finset.univ : Finset (Finset V)).filter (fun X => Tight ρ y X ∧ u ∈ X)
  have hunivD : Finset.univ ∈ FD := by
    simp only [FD, Finset.mem_filter, Finset.mem_univ, true_and, and_true]
    exact ((memBP_iff ρ y).1 hy).2
  obtain ⟨D, hDF, hDmin⟩ := FD.exists_min_image Finset.card ⟨_, hunivD⟩
  have hD : Tight ρ y D ∧ u ∈ D := by simpa [FD] using hDF
  have P1 : ∀ X, Tight ρ y X → u ∈ X → D ⊆ X := by
    intro X hX huX
    have ht := (tight_union_inter hρ hy hX hD.1).2
    have hc := hDmin (X ∩ D) (by simp [FD, ht, huX, hD.2])
    have := Finset.eq_of_subset_of_card_le (Finset.inter_subset_right : X ∩ D ⊆ D) hc
    rw [← this]; exact Finset.inter_subset_left
  -- `T`: a maximal tight set of `x` avoiding `u`
  let FT := (Finset.univ : Finset (Finset V)).filter (fun X => Tight ρ x X ∧ u ∉ X)
  have hemptyT : (∅ : Finset V) ∈ FT := by
    simp only [FT, Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty,
      not_false_eq_true, and_true]
    simp [Tight, sig, hρ.1]
  obtain ⟨T, hTF, hTmax⟩ := FT.exists_max_image Finset.card ⟨_, hemptyT⟩
  have hT : Tight ρ x T ∧ u ∉ T := by simpa [FT] using hTF
  have P2 : ∀ X, Tight ρ x X → u ∉ X → X ⊆ T := by
    intro X hX huX
    have ht := (tight_union_inter hρ hx hX hT.1).1
    have hc := hTmax (X ∪ T) (by simp [FT, ht, huX, hT.2])
    have := Finset.eq_of_subset_of_card_le (Finset.subset_union_right : T ⊆ X ∪ T) hc
    rw [this]; exact Finset.subset_union_left
  -- some `v ∈ D \ T` has `x(v) < y(v)`
  have hv : ∃ v ∈ D, x v < y v ∧ v ∉ T := by
    by_contra hno
    push_neg at hno
    have hle_x := ((memBP_iff ρ x).1 hx).1 (D ∪ T)
    have hle_y := ((memBP_iff ρ y).1 hy).1 (D ∩ T)
    have hsub := hρ.2.2 D T
    unfold Tight at hD hT
    rw [← hD.1, ← hT.1] at hsub
    have h3 := (add_le_add hle_x hle_y).trans hsub
    rw [← WithTop.coe_add, ← WithTop.coe_add, WithTop.coe_le_coe] at h3
    have h4 : sig x (D ∪ T) + sig y (D ∩ T) ≤ sig y D + sig x T := by exact_mod_cast h3
    have ex := sig_union_inter x D T
    have dx : sig x (D ∩ T) + sig x (D \ T) = sig x D := Finset.sum_inter_add_sum_sdiff _ _ _
    have dy : sig y (D ∩ T) + sig y (D \ T) = sig y D := Finset.sum_inter_add_sum_sdiff _ _ _
    have hlt : sig y (D \ T) < sig x (D \ T) := by
      apply Finset.sum_lt_sum
      · intro i hi
        rw [Finset.mem_sdiff] at hi
        by_contra hix
        push_neg at hix
        exact hi.2 (hno i hi.1 hix)
      · exact ⟨u, Finset.mem_sdiff.2 ⟨hD.2, hT.2⟩, hu'⟩
    omega
  obtain ⟨v, hvD, hxy, hvT⟩ := hv
  refine ⟨v, hxy, ?_, ?_⟩
  · exact move hint hx u v fun X hX hvX => by
      by_contra huX
      exact hvT (P2 X hX huX hvX)
  · have h := move hint hy v u fun X hX huX => P1 X hX huX hvD
    have e : (fun w => y w - CharVec v w + CharVec u w) = fun w => y w + CharVec u w - CharVec v w :=
      funext fun t => by ring
    rw [e] at h
    exact h

end backward

end MConvBase

open MConvBase in
theorem solution {V : Type*} [Fintype V] [DecidableEq V]
    (B : Set (V → ℤ)) (hB : B.Nonempty) :
    ExchangeAxiomB B ↔
      ∃ ρ : Finset V → WithTop ℝ, SubmodularSetFunction ρ ∧ IsIntegerValued ρ ∧
        B = {x : V → ℤ | (fun v => (x v : ℝ)) ∈ BasePolyhedron ρ} := by
  constructor
  · intro h
    obtain ⟨h1, h2⟩ := rho_props h hB
    refine ⟨rho B, h1, h2, Set.ext fun x => ⟨fun hx => subset_bp h hx, fun hx => bp_subset h hB x hx⟩⟩
  · rintro ⟨ρ, hρ, hint, rfl⟩
    exact backward hρ hint
