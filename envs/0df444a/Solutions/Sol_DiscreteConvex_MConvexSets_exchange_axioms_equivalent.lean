-- Prove2me | solution 1 for DiscreteConvex.MConvexSets.exchange_axioms_equivalent
-- status  : ACCEPTED   (prove)
-- author  : @Tim
-- created : 2026-10-05T18:06:56.447356+00:00
-- url     : https://prove2.me/submissions/ee72dbd3-5c15-48ba-bc16-cdef20b5b2ba

import Mathlib
import Definitions.Def_DiscreteConvex_MConvexSets_ExchangeAxiomB
import Definitions.Def_DiscreteConvex_MConvexSets_ExchangeAxiomBWeak
import Definitions.Def_DiscreteConvex_MConvexSets_ExchangeAxiomBPlus
import Definitions.Def_DiscreteConvex_MConvexSets_ExchangeAxiomBMinus

open DiscreteConvex.MConvexSets

namespace ExchTFAE

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

/-- `(B-EXC-[Z]) ⇒ (B-EXC[Z])`. -/
theorem minus_imp (B : Set (V → ℤ)) (hB : ExchangeAxiomBMinus B) : ExchangeAxiomB B := by
  suffices H : ∀ n, ∀ x ∈ B, ∀ y ∈ B, l1 x y = n → ∀ u ∈ SuppPos x y, ∃ v ∈ SuppNeg x y,
      (fun w => x w - CharVec u w + CharVec v w) ∈ B ∧
      (fun w => y w + CharVec u w - CharVec v w) ∈ B from
    fun x hx y hy u hu => H _ x hx y hy rfl u hu
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro x hx y hy hn u hu
  have hu' : y u < x u := hu
  obtain ⟨a, ha, hxa⟩ := hB x hx y hy u hu
  have ha' : x a < y a := ha
  obtain ⟨b, hb, hyb⟩ := hB y hy x hx a ha
  have hb' : y b < x b := hb
  have hua : u ≠ a := fun h => by subst h; omega
  have hab : a ≠ b := fun h => by subst h; omega
  by_cases hbu : b = u
  · subst hbu
    exact ⟨a, ha, hxa, mem_of_eq hyb fun t => by (simp only [CharVec] <;> split_ifs <;> subst_vars <;> first | omega | simp_all)⟩
  · have hu2 : u ∈ SuppPos x (fun w => y w - CharVec a w + CharVec b w) := by
      simp only [SuppPos, SuppNeg, Set.mem_ofPred_eq, CharVec, if_neg hua, if_neg (Ne.symm hbu)]
      omega
    obtain ⟨v, hv, hxv, hw⟩ :=
      ih _ (hn ▸ l1_y_step x y a b ha' hb') x hx _ hyb rfl u hu2
    have hv' : x v < y v - CharVec a v + CharVec b v := hv
    have hvb : v ≠ b := fun h => by subst h; simp only [CharVec, eq_self_iff_true, if_true, if_neg hab] at hv'; omega
    have hv'' : x v < y v := by
      simp only [CharVec, if_neg hvb] at hv'; split_ifs at hv' <;> omega
    have huv : u ≠ v := fun h => by subst h; omega
    have hbu' : b ≠ u := hbu
    obtain ⟨d, hd, hwd⟩ := hB _ hw y hy b (by
      simp only [SuppPos, SuppNeg, Set.mem_ofPred_eq, CharVec, if_neg hab.symm, eq_self_iff_true, if_true, if_neg hbu', if_neg (show b ≠ v from Ne.symm hvb)]
      omega)
    have hd' := hd; simp only [SuppPos, SuppNeg, Set.mem_ofPred_eq] at hd'
    have hdav : d = a ∨ d = v := by
      by_contra hc
      push_neg at hc
      simp only [CharVec, if_neg hc.1, if_neg hc.2] at hd'
      split_ifs at hd' <;> omega
    rcases hdav with rfl | rfl
    · exact ⟨v, hv'', hxv, mem_of_eq hwd fun t => by (simp only [CharVec] <;> split_ifs <;> subst_vars <;> first | omega | simp_all)⟩
    · exact ⟨a, ha, hxa, mem_of_eq hwd fun t => by (simp only [CharVec] <;> split_ifs <;> subst_vars <;> first | omega | simp_all)⟩

/-- `(B-EXC+[Z]) ⇒ (B-EXC[Z])`. -/
theorem plus_imp (B : Set (V → ℤ)) (hB : ExchangeAxiomBPlus B) : ExchangeAxiomB B := by
  suffices H : ∀ n, ∀ x ∈ B, ∀ y ∈ B, l1 x y = n → ∀ u ∈ SuppPos x y, ∃ v ∈ SuppNeg x y,
      (fun w => x w - CharVec u w + CharVec v w) ∈ B ∧
      (fun w => y w + CharVec u w - CharVec v w) ∈ B from
    fun x hx y hy u hu => H _ x hx y hy rfl u hu
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro x hx y hy hn u hu
  have hu' : y u < x u := hu
  obtain ⟨a, ha, hya⟩ := hB x hx y hy u hu
  have ha' : x a < y a := ha
  obtain ⟨b, hb, hxb⟩ := hB y hy x hx a ha
  have hb' : y b < x b := hb
  have hua : u ≠ a := fun h => by subst h; omega
  have hab : a ≠ b := fun h => by subst h; omega
  by_cases hbu : b = u
  · subst hbu
    exact ⟨a, ha, mem_of_eq hxb fun t => by (simp only [CharVec] <;> split_ifs <;> subst_vars <;> first | omega | simp_all), hya⟩
  · have hu2 : u ∈ SuppPos (fun w => x w + CharVec a w - CharVec b w) y := by
      simp only [SuppPos, SuppNeg, Set.mem_ofPred_eq, CharVec, if_neg hua, if_neg (Ne.symm hbu)]
      omega
    obtain ⟨v, hv, hw, hyv⟩ :=
      ih _ (hn ▸ l1_x_step x y a b ha' hb') _ hxb y hy rfl u hu2
    have hv' : x v + CharVec a v - CharVec b v < y v := hv
    have hvb : v ≠ b := fun h => by subst h; simp only [CharVec, eq_self_iff_true, if_true, if_neg hab] at hv'; omega
    have hv'' : x v < y v := by
      simp only [CharVec, if_neg hvb] at hv'; split_ifs at hv' <;> omega
    have huv : u ≠ v := fun h => by subst h; omega
    have hbu' : b ≠ u := hbu
    obtain ⟨d, hd, hwd⟩ := hB x hx _ hw b (by
      simp only [SuppPos, SuppNeg, Set.mem_ofPred_eq, CharVec, if_neg hab.symm, eq_self_iff_true, if_true, if_neg hbu', if_neg (show b ≠ v from Ne.symm hvb)]
      omega)
    have hd' := hd; simp only [SuppPos, SuppNeg, Set.mem_ofPred_eq] at hd'
    have hdav : d = a ∨ d = v := by
      by_contra hc
      push_neg at hc
      simp only [CharVec, if_neg hc.1, if_neg hc.2] at hd'
      split_ifs at hd' <;> omega
    rcases hdav with rfl | rfl
    · exact ⟨v, hv'', mem_of_eq hwd fun t => by (simp only [CharVec] <;> split_ifs <;> subst_vars <;> first | omega | simp_all), hyv⟩
    · exact ⟨a, ha, mem_of_eq hwd fun t => by (simp only [CharVec] <;> split_ifs <;> subst_vars <;> first | omega | simp_all), hya⟩

/-- `(B-EXCw[Z]) ⇒ (B-EXC[Z])` (set version of Murota–Shioura's argument). -/
theorem weak_imp (B : Set (V → ℤ)) (hB : ExchangeAxiomBWeak B) : ExchangeAxiomB B := by
  suffices H : ∀ n, ∀ x ∈ B, ∀ y ∈ B, l1 x y = n → ∀ u ∈ SuppPos x y, ∃ v ∈ SuppNeg x y,
      (fun w => x w - CharVec u w + CharVec v w) ∈ B ∧
      (fun w => y w + CharVec u w - CharVec v w) ∈ B from
    fun x hx y hy u hu => H _ x hx y hy rfl u hu
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro x hx y hy hn u hu
  have hu' : y u < x u := hu
  by_contra hno
  push_neg at hno
  -- `Q p q`: a `y`-side exchange with `p ≠ u`
  let Q : V → V → Prop := fun p q => p ∈ SuppPos x y ∧ p ≠ u ∧ q ∈ SuppNeg x y ∧
    (fun w => y w + CharVec p w - CharVec q w) ∈ B
  let Y : V → Prop := fun q => (fun w => y w + CharVec u w - CharVec q w) ∈ B
  have hxy : x ≠ y := fun h => by subst h; omega
  obtain ⟨u0, hu0, v0, hv0, hx0, hy0⟩ := hB x hx y hy hxy
  have hQ0 : Q u0 v0 := by
    refine ⟨hu0, fun h => ?_, hv0, hy0⟩
    subst h
    exact hno v0 hv0 hx0 hy0
  obtain ⟨u1, v1, hQ1, hpref⟩ : ∃ p q, Q p q ∧ ((∃ p' q', Q p' q' ∧ ¬ Y q') → ¬ Y q) := by
    by_cases hg : ∃ p' q', Q p' q' ∧ ¬ Y q'
    · obtain ⟨p, q, h1, h2⟩ := hg
      exact ⟨p, q, h1, fun _ => h2⟩
    · exact ⟨u0, v0, hQ0, fun h => absurd h hg⟩
  obtain ⟨hu1, hu1u, hv1, hy1⟩ := hQ1
  have hu1' : y u1 < x u1 := hu1
  have hv1' : x v1 < y v1 := hv1
  have huv1 : u ≠ v1 := fun h => by subst h; omega
  have hu1v1 : u1 ≠ v1 := fun h => by subst h; omega
  have hu2 : u ∈ SuppPos x (fun w => y w - CharVec v1 w + CharVec u1 w) := by
    simp only [SuppPos, SuppNeg, Set.mem_ofPred_eq, CharVec, if_neg huv1, if_neg (Ne.symm hu1u)]
    omega
  have hy1' : (fun w => y w - CharVec v1 w + CharVec u1 w) ∈ B := mem_of_eq hy1 fun t => by (simp only [CharVec] <;> split_ifs <;> subst_vars <;> first | omega | simp_all)
  obtain ⟨v, hv, hxv, hw⟩ := ih _ (hn ▸ l1_y_step x y v1 u1 hv1' hu1') x hx _ hy1' rfl u hu2
  have hv' : x v < y v - CharVec v1 v + CharVec u1 v := hv
  have hvu1 : v ≠ u1 := fun h => by
    subst h; simp only [CharVec, eq_self_iff_true, if_true, if_neg hu1v1] at hv'; omega
  have hv'' : x v < y v := by
    simp only [CharVec, if_neg hvu1] at hv'; split_ifs at hv' <;> omega
  have hYv : ¬ Y v := fun h => hno v hv'' hxv h
  have huv : u ≠ v := fun h => by subst h; omega
  have hu1u' : u1 ≠ u := hu1u
  have hwy : (fun w => (fun w => y w - CharVec v1 w + CharVec u1 w) w + CharVec u w - CharVec v w) ≠ y := by
    intro h
    have := congrFun h u1
    simp only [CharVec, eq_self_iff_true, if_true, if_neg hu1v1, if_neg hu1u', if_neg (Ne.symm hvu1)] at this
    omega
  obtain ⟨p, hp, q, hq, hwq, hyq⟩ := hB _ hw y hy hwy
  have hp' := hp; simp only [SuppPos, SuppNeg, Set.mem_ofPred_eq] at hp'
  have hq' := hq; simp only [SuppPos, SuppNeg, Set.mem_ofPred_eq] at hq'
  have hp2 : p = u1 ∨ p = u := by
    by_contra hc; push_neg at hc
    simp only [CharVec, if_neg hc.1, if_neg hc.2] at hp'
    split_ifs at hp' <;> omega
  have hq2 : q = v1 ∨ q = v := by
    by_contra hc; push_neg at hc
    simp only [CharVec, if_neg hc.1, if_neg hc.2] at hq'
    split_ifs at hq' <;> omega
  have key : (fun w => y w + CharVec u1 w - CharVec v w) ∈ B → ¬ Y v1 := fun h =>
    hpref ⟨u1, v, ⟨hu1, hu1u, hv'', h⟩, hYv⟩
  rcases hp2 with rfl | rfl <;> rcases hq2 with rfl | rfl
  · exact hYv (mem_of_eq hwq fun t => by (simp only [CharVec] <;> split_ifs <;> subst_vars <;> first | omega | simp_all))
  · exact key (mem_of_eq hyq fun t => by (simp only [CharVec] <;> split_ifs <;> subst_vars <;> first | omega | simp_all)) (mem_of_eq hwq fun t => by (simp only [CharVec] <;> split_ifs <;> subst_vars <;> first | omega | simp_all))
  · exact key (mem_of_eq hwq fun t => by (simp only [CharVec] <;> split_ifs <;> subst_vars <;> first | omega | simp_all)) (mem_of_eq hyq fun t => by (simp only [CharVec] <;> split_ifs <;> subst_vars <;> first | omega | simp_all))
  · exact hYv (mem_of_eq hyq fun t => by (simp only [CharVec] <;> split_ifs <;> subst_vars <;> first | omega | simp_all))

/-- `(B-EXC[Z]) ⇒ (B-EXCw[Z])`. -/
theorem imp_weak (B : Set (V → ℤ)) (hB : ExchangeAxiomB B) : ExchangeAxiomBWeak B := by
  intro x hx y hy hxy
  by_cases hp : ∃ u, y u < x u
  · obtain ⟨u, hu⟩ := hp
    obtain ⟨v, hv, h1, h2⟩ := hB x hx y hy u hu
    exact ⟨u, hu, v, hv, h1, h2⟩
  · push_neg at hp
    obtain ⟨w, hw⟩ : ∃ w, x w < y w := by
      by_contra h; push_neg at h
      exact hxy (funext fun t => le_antisymm (hp t) (h t))
    obtain ⟨v, hv, -⟩ := hB y hy x hx w hw
    exact absurd (hp v) (not_le.mpr hv)

end ExchTFAE

open ExchTFAE in
theorem solution {V : Type*} [Fintype V] [DecidableEq V] (B : Set (V → ℤ)) :
    [ExchangeAxiomB B, ExchangeAxiomBWeak B, ExchangeAxiomBPlus B, ExchangeAxiomBMinus B].TFAE := by
  tfae_have 1 → 2 := imp_weak B
  tfae_have 2 → 1 := weak_imp B
  tfae_have 1 → 3 := fun h x hx y hy u hu => by
    obtain ⟨v, hv, -, h2⟩ := h x hx y hy u hu
    exact ⟨v, hv, h2⟩
  tfae_have 3 → 1 := plus_imp B
  tfae_have 1 → 4 := fun h x hx y hy u hu => by
    obtain ⟨v, hv, h1, -⟩ := h x hx y hy u hu
    exact ⟨v, hv, h1⟩
  tfae_have 4 → 1 := minus_imp B
  tfae_finish
