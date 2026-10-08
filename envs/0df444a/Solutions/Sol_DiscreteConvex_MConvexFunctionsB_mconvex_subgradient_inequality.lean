-- Prove2me | solution 1 for DiscreteConvex.MConvexFunctionsB.mconvex_subgradient_inequality
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-06T00:12:19.014992+00:00
-- url     : https://prove2.me/submissions/d19ec7f7-3755-4fca-bd2e-b5b22b7e4c35

import Mathlib
import Definitions.Def_DiscreteConvex_MConvexFunctionsB_MExchangeAxiom
import Definitions.Def_DiscreteConvex_MConvexFunctionsB_DomZ
import Definitions.Def_DiscreteConvex_MConvexFunctionsB_FCheck



namespace DiscreteConvex.MConvexFunctionsB

theorem sub_key {V : Type*} [Fintype V] [DecidableEq V]
    (f : (V → ℤ) → WithTop ℝ) (hf : MExchangeAxiom f) (x : V → ℤ) (hx : x ∈ DomZ f)
    (A : ℝ) (hA : f x = A) :
    ∀ n : ℕ, ∀ y ∈ DomZ f, (∑ v, |y v - x v|).toNat = n →
      ∃ lam : V → V → ℕ,
        (∀ w, y w - x w = ∑ u, ∑ v, (lam u v : ℤ) * (CharVec v w - CharVec u w)) ∧
        (∀ u v, lam u v ≠ 0 → y u < x u ∧ x v < y v) ∧
        ∃ s : ℝ, (∑ u, ∑ v, (lam u v) • (f (fun w => x w - CharVec u w + CharVec v w) - f x))
            = (s : WithTop ℝ) ∧ ∃ B : ℝ, f y = B ∧ A + s ≤ B := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro y hy hn
  obtain ⟨B, hB⟩ := WithTop.ne_top_iff_exists.mp hy
  by_cases hxy : y = x
  · subst hxy
    refine ⟨fun _ _ => 0, fun w => by simp, fun u v h => absurd rfl h, 0, by simp, B, hB.symm, ?_⟩
    have : (A : WithTop ℝ) = B := hA.symm.trans hB.symm
    simp at this; simp [this]
  -- find a with x a < y a
  have hex : ∃ a, x a < y a := by
    by_contra hne
    push_neg at hne
    have : ∃ b, y b < x b := by
      by_contra h2; push_neg at h2
      exact hxy (funext fun w => le_antisymm (hne w) (h2 w))
    obtain ⟨b, hb⟩ := this
    obtain ⟨v, hv, -⟩ := hf x hx y hy b (by simp [SuppPos, hb])
    simp [SuppNeg] at hv
    exact absurd (hne v) (not_le.mpr hv)
  obtain ⟨a, ha⟩ := hex
  obtain ⟨b, hb, hexc⟩ := hf y hy x hx a (by simp [SuppPos, ha])
  simp only [SuppNeg, Finset.mem_filter, Finset.mem_univ, true_and] at hb
  have hab : a ≠ b := by intro h; subst h; exact lt_asymm ha hb
  set y' : V → ℤ := fun w => y w - CharVec a w + CharVec b w with hy'
  set x' : V → ℤ := fun w => x w + CharVec a w - CharVec b w with hx'
  rw [← hB, hA] at hexc
  have hC : f y' ≠ ⊤ := by
    intro h; rw [h] at hexc; simp at hexc
  have hD : f x' ≠ ⊤ := by
    intro h; rw [h] at hexc; simp at hexc
  obtain ⟨C, hC'⟩ := WithTop.ne_top_iff_exists.mp hC
  obtain ⟨D, hD'⟩ := WithTop.ne_top_iff_exists.mp hD
  rw [← hC', ← hD'] at hexc
  have hexcR : C + D ≤ B + A := by exact_mod_cast hexc
  have hca : CharVec a a = 1 := by simp [CharVec]
  have hcb : CharVec b b = 1 := by simp [CharVec]
  have hcab : CharVec a b = 0 := by simp [CharVec, Ne.symm hab]
  have hcba : CharVec b a = 0 := by simp [CharVec, hab]
  have hlt : (∑ v, |y' v - x v|) < ∑ v, |y v - x v| := by
    apply Finset.sum_lt_sum
    · intro w _
      simp only [hy', CharVec]
      split_ifs <;> subst_vars <;> first | (exfalso; omega) | (rw [abs_le]; constructor <;> cases abs_cases (y w - x w) <;> omega) | simp
    · refine ⟨a, Finset.mem_univ _, ?_⟩
      simp only [hy', hca, hcba]
      rw [abs_of_nonneg (by omega), abs_of_pos (by omega)]; omega
  have hnn : 0 ≤ ∑ v, |y' v - x v| := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  obtain ⟨lam, hroute, hsupp, s, hs, C2, hC2, hle⟩ :=
    ih _ (by omega) y' (by simpa [DomZ] using hC) rfl
  rw [← hC', WithTop.coe_eq_coe] at hC2
  subst hC2
  let del : V → V → ℕ := fun u v => if u = b then (if v = a then 1 else 0) else 0
  refine ⟨fun u v => lam u v + del u v, ?_, ?_, s + (D - A), ?_, B, hB.symm, by linarith⟩
  · intro w
    have h1 := hroute w
    simp only [hy'] at h1
    simp only [Nat.cast_add, add_mul, Finset.sum_add_distrib, del]
    rw [← h1]
    simp [apply_ite (fun n : ℕ => (n : ℤ)), ite_mul]
    ring
  · intro u v huv
    by_cases hl : lam u v = 0
    · have : del u v ≠ 0 := by simpa [hl] using huv
      simp only [del] at this
      split_ifs at this with h1 h2
      · subst h1; subst h2; exact ⟨hb, ha⟩
      · simp at this
      · simp at this
    · obtain ⟨h1, h2⟩ := hsupp u v hl
      simp only [hy', CharVec] at h1 h2
      constructor
      · by_cases hua : u = a
        · subst hua; exact absurd h1 (by simp [hab]; omega)
        · by_cases hub : u = b
          · subst hub; exact hb
          · simp [hua, hub] at h1; exact h1
      · by_cases hva : v = a
        · subst hva; exact ha
        · by_cases hvb : v = b
          · subst hvb; exact absurd h2 (by simp [Ne.symm hab]; omega)
          · simp [hva, hvb] at h2; exact h2
  · simp only [add_smul, Finset.sum_add_distrib, hs, del]
    rw [Finset.sum_eq_single b (fun u _ hu => by simp [hu]) (by simp),
      Finset.sum_eq_single a (fun v _ hv => by simp [hv]) (by simp)]
    simp only [if_true, one_smul]
    have : (fun w => x w - CharVec b w + CharVec a w) = x' := by
      funext w; simp only [hx']; ring
    rw [this, ← hD', hA, ← WithTop.LinearOrderedAddCommGroup.coe_sub, ← WithTop.coe_add]


theorem cv_self {V : Type*} [DecidableEq V] (x : V → ℤ) (u : V) :
    (fun w => x w - CharVec u w + CharVec u w) = x := by funext w; ring

theorem tri {V : Type*} [Fintype V] [DecidableEq V]
    (f : (V → ℤ) → WithTop ℝ) (hf : MExchangeAxiom f) (x : V → ℤ)
    (A : ℝ) (hA : f x = A) (u v w : V) (a1 a2 : ℝ)
    (h1 : f (fun t => x t - CharVec u t + CharVec v t) = a1)
    (h2 : f (fun t => x t - CharVec v t + CharVec w t) = a2) :
    ∃ a3 : ℝ, f (fun t => x t - CharVec u t + CharVec w t) = a3 ∧ a3 + A ≤ a1 + a2 := by
  by_cases huv : u = v
  · subst huv; rw [cv_self, hA] at h1
    have : A = a1 := WithTop.coe_injective h1
    exact ⟨a2, h2, by linarith⟩
  by_cases hvw : v = w
  · subst hvw; rw [cv_self, hA] at h2
    have : A = a2 := WithTop.coe_injective h2
    exact ⟨a1, h1, by linarith⟩
  have hx1 : (fun t => x t - CharVec u t + CharVec v t) ∈ DomZ f := by
    simp only [DomZ, Set.mem_setOf_eq]; rw [h1]; exact WithTop.coe_ne_top
  have hx2 : (fun t => x t - CharVec v t + CharVec w t) ∈ DomZ f := by
    simp only [DomZ, Set.mem_setOf_eq]; rw [h2]; exact WithTop.coe_ne_top
  obtain ⟨v', hv', hex⟩ := hf _ hx1 _ hx2 v (by
    simp only [SuppPos, Finset.mem_filter, Finset.mem_univ, true_and]
    simp only [CharVec, if_true, hvw, Ne.symm huv, if_false]; omega)
  simp only [SuppNeg, Finset.mem_filter, Finset.mem_univ, true_and] at hv'
  beta_reduce at hex
  rw [h1, h2] at hex
  have hcase : v' = u ∨ v' = w := by
    by_contra hc; push_neg at hc
    simp [CharVec, hc.1, hc.2] at hv'
    split_ifs at hv' <;> omega
  have key : ∃ a3 : ℝ, f (fun t => x t - CharVec u t + CharVec w t) = a3 ∧ a3 + A ≤ a1 + a2 := by
    rcases hcase with rfl | rfl
    · have e1 : (fun t => x t - CharVec v' t + CharVec v t - CharVec v t + CharVec v' t) = x := by
        funext t; ring
      have e2 : (fun t => x t - CharVec v t + CharVec w t + CharVec v t - CharVec v' t) =
          (fun t => x t - CharVec v' t + CharVec w t) := by funext t; ring
      rw [e1, e2, hA] at hex
      have hne : f (fun t => x t - CharVec v' t + CharVec w t) ≠ ⊤ := by
        intro h; rw [h] at hex; simp at hex
      obtain ⟨a3, ha3⟩ := WithTop.ne_top_iff_exists.mp hne
      rw [← ha3] at hex
      refine ⟨a3, ha3.symm, ?_⟩
      have : (A + a3 : ℝ) ≤ a1 + a2 := by exact_mod_cast hex
      linarith
    · have e1 : (fun t => x t - CharVec u t + CharVec v t - CharVec v t + CharVec v' t) =
          (fun t => x t - CharVec u t + CharVec v' t) := by funext t; ring
      have e2 : (fun t => x t - CharVec v t + CharVec v' t + CharVec v t - CharVec v' t) = x := by
        funext t; ring
      rw [e1, e2, hA] at hex
      have hne : f (fun t => x t - CharVec u t + CharVec v' t) ≠ ⊤ := by
        intro h; rw [h] at hex; simp at hex
      obtain ⟨a3, ha3⟩ := WithTop.ne_top_iff_exists.mp hne
      rw [← ha3] at hex
      refine ⟨a3, ha3.symm, ?_⟩
      have : (a3 + A : ℝ) ≤ a1 + a2 := by exact_mod_cast hex
      linarith
  exact key

theorem potential {V : Type*} [Fintype V] [DecidableEq V]
    (f : (V → ℤ) → WithTop ℝ) (hf : MExchangeAxiom f) (x : V → ℤ)
    (A : ℝ) (hA : f x = A) :
    ∃ P : V → ℝ, ∀ u v (r : ℝ), f (fun t => x t - CharVec u t + CharVec v t) = r →
      P v - P u ≤ r - A := by
  have hQ : ∀ v, ∃ q : ℝ, ∃ u0, f (fun t => x t - CharVec u0 t + CharVec v t) = q ∧
      ∀ u, (q : WithTop ℝ) ≤ f (fun t => x t - CharVec u t + CharVec v t) := by
    intro v
    obtain ⟨u0, -, hu0⟩ := Finset.exists_mem_eq_inf (Finset.univ : Finset V) ⟨v, Finset.mem_univ v⟩
      (fun u => f (fun t => x t - CharVec u t + CharVec v t))
    have hle : f (fun t => x t - CharVec u0 t + CharVec v t) ≤ f x := by
      rw [← hu0]
      have := Finset.inf_le (f := fun u => f (fun t => x t - CharVec u t + CharVec v t))
        (Finset.mem_univ v)
      simpa [cv_self] using this
    have hne : f (fun t => x t - CharVec u0 t + CharVec v t) ≠ ⊤ := by
      intro h; rw [h, hA] at hle; simp at hle
    obtain ⟨q, hq⟩ := WithTop.ne_top_iff_exists.mp hne
    refine ⟨q, u0, hq.symm, fun u => ?_⟩
    rw [hq, ← hu0]
    exact Finset.inf_le (Finset.mem_univ u)
  choose P u0 hP0 hPle using hQ
  refine ⟨P, fun u v r hr => ?_⟩
  obtain ⟨a3, ha3, hle⟩ := tri f hf x A hA (u0 u) u v (P u) r (hP0 u) hr
  have := hPle v (u0 u)
  rw [ha3] at this
  have : P v ≤ a3 := by exact_mod_cast this
  linarith



theorem subgrad_core {V : Type*} [Fintype V] [DecidableEq V]
    (f : (V → ℤ) → WithTop ℝ) (hf : MExchangeAxiom f) (x y : V → ℤ) (hx : x ∈ DomZ f)
    (hy : y ∈ DomZ f) :
    f y ≥ f x + FCheck f x y := by
  obtain ⟨A, hA⟩ := WithTop.ne_top_iff_exists.mp hx
  obtain ⟨lam, hroute, -, s, hs, B, hB, hle⟩ := sub_key f hf x hx A hA.symm _ y hy rfl
  obtain ⟨P, hP⟩ := potential f hf x A hA.symm
  have hbound : ∀ lam' : V → V → ℕ,
      (∀ w, y w - x w = ∑ u, ∑ v, (lam' u v : ℤ) * (CharVec v w - CharVec u w)) →
      ((∑ w, P w * ((y w - x w : ℤ) : ℝ) : ℝ) : WithTop ℝ) ≤
        ∑ u, ∑ v, (lam' u v) • (f (fun w => x w - CharVec u w + CharVec v w) - f x) := by
    intro lam' hr
    have alg : (∑ w, P w * ((y w - x w : ℤ) : ℝ)) =
        ∑ u, ∑ v, (lam' u v : ℝ) * (P v - P u) := by
      simp_rw [hr]
      push_cast
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun u _ => ?_)
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun v _ => ?_)
      simp only [CharVec, mul_sub]
      rw [Finset.sum_sub_distrib]
      push_cast
      simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
      ring
    rw [alg, WithTop.coe_sum]
    refine Finset.sum_le_sum (fun u _ => ?_)
    rw [WithTop.coe_sum]
    refine Finset.sum_le_sum (fun v _ => ?_)
    by_cases hl : lam' u v = 0
    · simp [hl]
    by_cases htop : f (fun w => x w - CharVec u w + CharVec v w) = ⊤
    · rw [htop, ← hA]
      rw [WithTop.LinearOrderedAddCommGroup.top_sub]
      obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hl
      rw [hk, succ_nsmul, WithTop.add_top]
      exact le_top
    obtain ⟨r, hr'⟩ := WithTop.ne_top_iff_exists.mp htop
    rw [← hr', ← hA, ← WithTop.LinearOrderedAddCommGroup.coe_sub, ← WithTop.coe_nsmul, WithTop.coe_le_coe, nsmul_eq_mul]
    have := hP u v r hr'.symm
    exact mul_le_mul_of_nonneg_left this (by positivity)
  have h1 : FCheck f x y ≤ s := by
    unfold FCheck
    set S := {L : WithTop ℝ | ∃ lam : V → V → ℕ,
      (∀ w, y w - x w = ∑ u, ∑ v, (lam u v : ℤ) * (CharVec v w - CharVec u w)) ∧
      L = ∑ u, ∑ v, (lam u v) • (f (fun w => x w - CharVec u w + CharVec v w) - f x)} with hS
    have hmem : (s : WithTop ℝ) ∈ S := ⟨lam, hroute, hs.symm⟩
    have hbdd : BddBelow S := ⟨_, fun L ⟨lam', hr, hL⟩ => hL ▸ hbound lam' hr⟩
    have hns : ¬ S ⊆ {⊤} := fun h => by simpa using h hmem
    rw [WithTop.sInf_eq hns hbdd]
    rw [WithTop.coe_le_coe]
    refine csInf_le ⟨∑ w, P w * ((y w - x w : ℤ) : ℝ), fun z hz => ?_⟩ hmem
    have := hbdd
    obtain ⟨lam', hr, hL⟩ := hz
    have := hbound lam' hr
    rw [← hL] at this
    exact_mod_cast this
  calc f x + FCheck f x y ≤ f x + s := add_le_add le_rfl h1
    _ = ((A + s : ℝ) : WithTop ℝ) := by rw [← hA]; rfl
    _ ≤ f y := by rw [hB]; exact_mod_cast hle

end DiscreteConvex.MConvexFunctionsB

open DiscreteConvex.MConvexFunctionsB


theorem solution {V : Type*} [Fintype V] [DecidableEq V]
    (f : (V → ℤ) → WithTop ℝ) (hf : MExchangeAxiom f) (x y : V → ℤ) (hx : x ∈ DomZ f)
    (hy : y ∈ DomZ f) :
    f y ≥ f x + FCheck f x y := by
  exact subgrad_core f hf x y hx hy
