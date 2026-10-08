-- Prove2me | solution 1 for DiscreteConvex.MConvexSetsB.mconvex_hole_free
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-06T02:08:06.944999+00:00
-- url     : https://prove2.me/submissions/189bc8d9-2b49-4221-84a4-3a51e9dafbfc

import Mathlib
import Definitions.Def_DiscreteConvex_MConvexSetsB_ExchangeAxiomB
import Definitions.Def_DiscreteConvex_MConvexSetsB_IntEmbed
import Definitions.Def_DiscreteConvex_MConvexSetsB_IntPts



namespace DiscreteConvex.MConvexSetsB

section ExchCore

variable {V : Type*} [Fintype V] [DecidableEq V]

def Dst (a b : V → ℤ) : ℤ := ∑ w, |a w - b w|

lemma Dst_nonneg (a b : V → ℤ) : 0 ≤ Dst a b :=
  Finset.sum_nonneg (fun w _ => abs_nonneg _)

lemma Dst_zero {a b : V → ℤ} (h : Dst a b = 0) : a = b := by
  funext w
  have := (Finset.sum_eq_zero_iff_of_nonneg (fun w _ => abs_nonneg (a w - b w))).mp h w
    (Finset.mem_univ w)
  have := abs_eq_zero.mp this
  linarith

lemma sum_cv (p : V) : ∑ w, CharVec p w = 1 := by
  simp [CharVec]

lemma cv_nonneg (p w : V) : 0 ≤ CharVec p w := by
  unfold CharVec; split_ifs <;> norm_num

lemma Dst_move (a b : V → ℤ) (p q : V) (hp : b p < a p) (hq : a q < b q) :
    Dst (fun w => a w - CharVec p w + CharVec q w) b = Dst a b - 2 := by
  have hpq : p ≠ q := by intro h; subst h; omega
  unfold Dst
  have h : ∀ w, |a w - CharVec p w + CharVec q w - b w| =
      |a w - b w| - (CharVec p w + CharVec q w) := by
    intro w
    by_cases hwp : w = p
    · subst hwp; simp only [CharVec, if_pos rfl, if_neg hpq]
      rw [abs_of_nonneg (by omega), abs_of_pos (by omega)]; ring
    by_cases hwq : w = q
    · subst hwq; simp only [CharVec, if_pos rfl, if_neg (Ne.symm hpq)]
      rw [abs_of_nonpos (by omega), abs_of_neg (by omega)]; ring
    simp only [CharVec, if_neg hwp, if_neg hwq]; ring_nf
  simp only [h, Finset.sum_sub_distrib, Finset.sum_add_distrib, sum_cv]
  ring


lemma sum_cv_mem (X : Finset V) (b : V) (hb : b ∈ X) : ∑ v ∈ X, CharVec b v = 1 := by
  simp [CharVec, hb]

lemma sum_cv_nmem (X : Finset V) (b : V) (hb : b ∉ X) : ∑ v ∈ X, CharVec b v = 0 := by
  simp [CharVec, hb]

open Classical in
theorem hole_int (B : Set (V → ℤ)) (hExc : ExchangeAxiomB B) (hBne : B.Nonempty) (y : V → ℤ)
    (hle : ∀ X : Finset V, ∀ c : ℤ, (∀ w ∈ B, ∑ v ∈ X, w v ≤ c) → ∑ v ∈ X, y v ≤ c)
    (hge : ∀ X : Finset V, ∀ c : ℤ, (∀ w ∈ B, c ≤ ∑ v ∈ X, w v) → c ≤ ∑ v ∈ X, y v) :
    y ∈ B := by
  -- closest point
  have hex : ∃ n : ℕ, ∃ x ∈ B, (Dst x y).toNat = n := by
    obtain ⟨x, hx⟩ := hBne; exact ⟨_, x, hx, rfl⟩
  obtain ⟨x, hxB, hxn⟩ := Nat.find_spec hex
  have hmin : ∀ x' ∈ B, Dst x y ≤ Dst x' y := by
    intro x' hx'
    have h1 := Nat.find_min' hex ⟨x', hx', rfl⟩
    have := Dst_nonneg x y; have := Dst_nonneg x' y
    omega
  by_contra hyB
  have hxy : x ≠ y := by intro h; rw [h] at hxB; exact hyB hxB
  -- sums are constant on B
  have hsum : ∀ n : ℕ, ∀ a ∈ B, ∀ b ∈ B, Dst a b = n → ∑ v, a v = ∑ v, b v := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
    intro a ha b hb hD
    by_cases hab : a = b
    · rw [hab]
    by_cases hp : ∃ u, b u < a u
    · obtain ⟨u, hu⟩ := hp
      obtain ⟨v, hv, ha', _⟩ := hExc a ha b hb u hu
      have hv' : a v < b v := hv
      have hD' := Dst_move a b u v hu hv'
      have := Dst_nonneg (fun w => a w - CharVec u w + CharVec v w) b
      have e := ih (n-2) (by omega) _ ha' b hb (by omega)
      rw [← e]; simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, sum_cv]; ring
    · push_neg at hp
      obtain ⟨u, hu⟩ : ∃ u, a u < b u := by
        by_contra hc; push_neg at hc; exact hab (funext fun w => le_antisymm (hp w) (hc w))
      obtain ⟨v, hv, hb', _⟩ := hExc b hb a ha u hu
      have hv' : b v < a v := hv
      have hD' := Dst_move b a u v hu hv'
      have hsym : Dst a b = Dst b a := by
        unfold Dst; exact Finset.sum_congr rfl (fun w _ => abs_sub_comm _ _)
      have := Dst_nonneg (fun w => b w - CharVec u w + CharVec v w) a
      have e := ih (n-2) (by omega) _ hb' a ha (by omega)
      rw [e.symm.trans (by simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, sum_cv]; ring)]
  have hsB : ∀ w ∈ B, ∑ v, w v = ∑ v, x v := by
    intro w hw
    have := Dst_nonneg w x
    exact hsum (Dst w x).toNat w hw x hxB (by omega)
  have hsy : ∑ v, y v = ∑ v, x v := by
    apply le_antisymm
    · exact hle Finset.univ _ (fun w hw => (hsB w hw).le)
    · exact hge Finset.univ _ (fun w hw => (hsB w hw).ge)
  -- a deficient coordinate
  obtain ⟨b0, hb0⟩ : ∃ b, x b < y b := by
    by_contra hc; push_neg at hc
    apply hxy
    have := (Finset.sum_eq_sum_iff_of_le (s := Finset.univ) (fun v _ => hc v)).mp hsy
    funext v; exact (this v (Finset.mem_univ v)).symm
  -- arcs
  let arc : V → V → Prop := fun a b => (fun w => x w - CharVec a w + CharVec b w) ∈ B
  have hclose : ∀ a b, y a < x a → x b < y b → ¬ arc a b := by
    intro a b ha hb harc
    have h1 := Dst_move x y a b ha hb
    have h2 := hmin _ harc
    omega
  have htrans : ∀ a b c, arc a b → arc b c → a ≠ c → arc a c := by
    intro a b c hab hbc hac
    by_cases hab' : a = b
    · subst hab'; exact hbc
    by_cases hbc' : b = c
    · subst hbc'; exact hab
    have hb : b ∈ SuppPos (fun w => x w - CharVec a w + CharVec b w)
        (fun w => x w - CharVec b w + CharVec c w) := by
      show x b - CharVec b b + CharVec c b < x b - CharVec a b + CharVec b b
      simp [CharVec, hab', Ne.symm hab', hbc', Ne.symm hbc']
    obtain ⟨w, hw, h1, h2⟩ := hExc _ hab _ hbc b hb
    have hw' : x w - CharVec a w + CharVec b w < x w - CharVec b w + CharVec c w := hw
    by_cases hwc : w = c
    · subst hwc
      show (fun v => x v - CharVec a v + CharVec w v) ∈ B
      convert h1 using 1; funext v; simp only [CharVec]; split_ifs <;> omega
    by_cases hwa : w = a
    · subst hwa
      show (fun v => x v - CharVec w v + CharVec c v) ∈ B
      convert h2 using 1; funext v; simp only [CharVec]; split_ifs <;> omega
    exfalso
    simp only [CharVec, if_neg hwc, if_neg hwa] at hw'
    split_ifs at hw' <;> omega
  -- the set X
  let X : Finset V := Finset.univ.filter (fun a => ∃ b, x b < y b ∧ (a = b ∨ arc a b))
  have hXS : ∀ a ∈ X, x a ≤ y a := by
    intro a ha
    simp only [X, Finset.mem_filter, Finset.mem_univ, true_and] at ha
    obtain ⟨b, hb, hab⟩ := ha
    by_contra hc; push_neg at hc
    rcases hab with rfl | harc
    · omega
    · exact hclose a b hc hb harc
  have hXcl : ∀ a b, arc a b → b ∈ X → a ∈ X := by
    intro a b hab hbX
    simp only [X, Finset.mem_filter, Finset.mem_univ, true_and] at hbX ⊢
    obtain ⟨c, hc, hbc⟩ := hbX
    refine ⟨c, hc, ?_⟩
    rcases hbc with rfl | hbc
    · exact Or.inr hab
    · by_cases hac : a = c
      · exact Or.inl hac
      · exact Or.inr (htrans a b c hab hbc hac)
  -- global optimality of x for χ_X
  have hopt : ∀ n : ℕ, ∀ w ∈ B, Dst w x = n → ∑ v ∈ X, w v ≤ ∑ v ∈ X, x v := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
    intro w hw hD
    by_contra hc; push_neg at hc
    obtain ⟨b, hbX, hb⟩ : ∃ b ∈ X, x b < w b := by
      by_contra h; push_neg at h
      exact absurd (Finset.sum_le_sum h) (not_le.mpr hc)
    obtain ⟨a, ha, hw', hx'⟩ := hExc w hw x hxB b hb
    have ha' : w a < x a := ha
    have harc : arc a b := by
      show (fun v => x v - CharVec a v + CharVec b v) ∈ B
      convert hx' using 1; funext v; ring
    have haX := hXcl a b harc hbX
    have hD' := Dst_move w x b a hb ha'
    have := Dst_nonneg (fun v => w v - CharVec b v + CharVec a v) x
    have e := ih (n-2) (by omega) _ hw' (by omega)
    have : ∑ v ∈ X, (w v - CharVec b v + CharVec a v) = ∑ v ∈ X, w v := by
      rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, sum_cv_mem X b hbX, sum_cv_mem X a haX]
      ring
    rw [this] at e
    omega
  have hXle : ∑ v ∈ X, y v ≤ ∑ v ∈ X, x v := by
    apply hle X
    intro w hw
    have := Dst_nonneg w x
    exact hopt (Dst w x).toNat w hw (by omega)
  have hb0X : b0 ∈ X := by
    simp only [X, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨b0, hb0, Or.inl rfl⟩
  have : ∑ v ∈ X, x v < ∑ v ∈ X, y v :=
    Finset.sum_lt_sum (fun v hv => hXS v hv) ⟨b0, hb0X, hb0⟩
  omega

theorem hole_core (B : Set (V → ℤ)) (hExc : ExchangeAxiomB B) (hBne : B.Nonempty) :
    IntEmbed B = convexHull ℝ (IntEmbed B) ∩ IntPts := by
  ext q
  constructor
  · intro hq
    refine ⟨subset_convexHull ℝ _ hq, ?_⟩
    obtain ⟨x, _, rfl⟩ := hq
    intro v; exact ⟨x v, rfl⟩
  · rintro ⟨hq, hint⟩
    choose yZ hyZ using hint
    have hconv : ∀ X : Finset V, ∀ σ c : ℝ, (∀ w ∈ B, σ * ∑ v ∈ X, (w v : ℝ) ≤ c) →
        σ * ∑ v ∈ X, q v ≤ c := by
      intro X σ c h
      have hH : Convex ℝ {r : V → ℝ | σ * ∑ v ∈ X, r v ≤ c} := by
        intro a ha b hb s t hs ht hst
        simp only [Set.mem_setOf_eq] at ha hb ⊢
        have e : σ * ∑ v ∈ X, (s • a + t • b) v = s * (σ * ∑ v ∈ X, a v) + t * (σ * ∑ v ∈ X, b v) := by
          simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
            ← Finset.mul_sum]; ring
        rw [e]
        calc s * (σ * ∑ v ∈ X, a v) + t * (σ * ∑ v ∈ X, b v) ≤ s * c + t * c :=
              add_le_add (mul_le_mul_of_nonneg_left ha hs) (mul_le_mul_of_nonneg_left hb ht)
          _ = c := by rw [← add_mul, hst, one_mul]
      have hsub : IntEmbed B ⊆ {r : V → ℝ | σ * ∑ v ∈ X, r v ≤ c} := by
        rintro _ ⟨w, hw, rfl⟩; exact h w hw
      exact convexHull_min hsub hH hq
    have hle : ∀ X : Finset V, ∀ c : ℤ, (∀ w ∈ B, ∑ v ∈ X, w v ≤ c) → ∑ v ∈ X, yZ v ≤ c := by
      intro X c h
      have := hconv X 1 c (fun w hw => by rw [one_mul]; exact_mod_cast h w hw)
      simp only [hyZ, one_mul] at this
      exact_mod_cast this
    have hge : ∀ X : Finset V, ∀ c : ℤ, (∀ w ∈ B, c ≤ ∑ v ∈ X, w v) → c ≤ ∑ v ∈ X, yZ v := by
      intro X c h
      have := hconv X (-1) (-c) (fun w hw => by
        have h2 : ((c : ℤ) : ℝ) ≤ ∑ v ∈ X, ((w v : ℤ) : ℝ) := by exact_mod_cast h w hw
        linarith)
      simp only [hyZ] at this
      have h3 : ((c : ℤ) : ℝ) ≤ ∑ v ∈ X, ((yZ v : ℤ) : ℝ) := by linarith
      exact_mod_cast h3
    have hy := hole_int B hExc hBne yZ hle hge
    exact ⟨yZ, hy, funext fun v => (hyZ v).symm⟩

end ExchCore

end DiscreteConvex.MConvexSetsB

open DiscreteConvex.MConvexSetsB


theorem solution {V : Type*} [Fintype V] [DecidableEq V] (B : Set (V → ℤ))
    (hExc : ExchangeAxiomB B) (hBne : B.Nonempty) :
    IntEmbed B = convexHull ℝ (IntEmbed B) ∩ IntPts := by
  exact hole_core B hExc hBne
