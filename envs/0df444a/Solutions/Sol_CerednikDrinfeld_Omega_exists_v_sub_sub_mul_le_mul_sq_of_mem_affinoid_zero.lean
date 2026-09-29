-- Prove2me | solution 1 for CerednikDrinfeld.Omega.exists_v_sub_sub_mul_le_mul_sq_of_mem_affinoid_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/18f16739-d3af-532b-85e7-527fb5de4a45

import Definitions.Def_CerednikDrinfeld_DrinfeldHolomorphic
import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_Omega_exists_v_sub_sub_mul_le_mul_sq_of_mem_affinoid_zero

set_option autoImplicit false

open Filter Polynomial
open scoped Topology
open CerednikDrinfeld.Omega

namespace P2mKcDiscTaylor

variable {K : Type} [Field K] {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]

theorem eq_one_of_prod_eq_one {s : Multiset Γ₀} (hle : ∀ x ∈ s, x ≤ 1) (hprod : s.prod = 1) :
    ∀ x ∈ s, x = 1 := by
  induction s using Multiset.induction with
  | empty => simp
  | cons a s ih =>
    intro x hx
    rw [Multiset.prod_cons] at hprod
    have ha : a ≤ 1 := hle a (Multiset.mem_cons_self a s)
    have hs : s.prod ≤ 1 := by
      have := Multiset.prod_map_le_prod_map (s := s) id (fun _ => (1 : Γ₀))
        fun y hy => hle y (Multiset.mem_cons_of_mem hy)
      simpa using this
    have ha1 : a = 1 := by
      by_contra hne
      have hlt : a < 1 := lt_of_le_of_ne ha hne
      have : a * s.prod < 1 := mul_lt_one_of_lt_of_le hlt hs
      exact this.ne hprod
    rw [ha1, one_mul] at hprod
    rcases Multiset.mem_cons.1 hx with rfl | hx
    · exact ha1
    · exact ih (fun y hy => hle y (Multiset.mem_cons_of_mem hy)) hprod x hx

theorem exists_generic_unit [IsAlgClosed K] (T : Multiset K) (hT : ∀ b ∈ T, Valued.v b ≤ 1) :
    ∃ u : K, Valued.v u = 1 ∧ ∀ b ∈ T, Valued.v (u - b) = 1 := by
  set T' : Multiset K := 0 ::ₘ T with hT'
  have hT'le : ∀ b ∈ T', Valued.v b ≤ 1 := fun b hb => by
    rcases Multiset.mem_cons.1 hb with rfl | hb
    · simp
    · exact hT b hb
  set F : K[X] := (T'.map fun b => X - C b).prod + 1 with hF
  have hmonic : (T'.map fun b => X - C b).prod.Monic := by
    refine monic_multiset_prod_of_monic _ _ fun b _ => monic_X_sub_C b
  have hdegprod : (T'.map fun b => X - C b).prod.natDegree = Multiset.card T' := by
    rw [natDegree_multiset_prod_of_monic]
    · simp
    · intro f hf
      obtain ⟨b, -, rfl⟩ := Multiset.mem_map.1 hf
      exact monic_X_sub_C b
  have hcard : 0 < Multiset.card T' := by rw [hT', Multiset.card_cons]; omega
  have hFdeg : F.degree ≠ 0 := by
    have h1 : F.natDegree = Multiset.card T' := by
      rw [hF, natDegree_add_eq_left_of_degree_lt, hdegprod]
      rw [degree_one, degree_eq_natDegree hmonic.ne_zero, hdegprod]
      exact_mod_cast hcard
    intro h0
    have := natDegree_eq_zero_iff_degree_le_zero.2 h0.le
    omega
  obtain ⟨u, hu⟩ := IsAlgClosed.exists_root F hFdeg
  have hprod : (T'.map fun b => u - b).prod = -1 := by
    have h := hu
    rw [IsRoot, hF, eval_add, eval_one, eval_multiset_prod, Multiset.map_map, add_eq_zero_iff_eq_neg] at h
    convert h using 2 <;> try rfl
    refine Multiset.map_congr rfl fun b _ => ?_
    simp
  have hvprod : (T'.map fun b => Valued.v (u - b)).prod = 1 := by
    have := congrArg Valued.v hprod
    rw [Valuation.map_neg, Valuation.map_one, map_multiset_prod, Multiset.map_map] at this
    exact this

  have hule : Valued.v u ≤ 1 := by
    by_contra hgt
    push Not at hgt
    have hfac : ∀ b ∈ T', Valued.v (u - b) = Valued.v u := fun b hb =>
      Valuation.map_sub_eq_of_lt_left _ ((hT'le b hb).trans_lt hgt)
    have : (T'.map fun b => Valued.v (u - b)).prod = (T'.map fun _ => Valued.v u).prod :=
      congrArg Multiset.prod (Multiset.map_congr rfl hfac)
    rw [hvprod, Multiset.map_const', Multiset.prod_replicate] at this
    have h1 : (1 : Γ₀) < Valued.v u ^ Multiset.card T' := one_lt_pow₀ hgt hcard.ne'
    exact h1.ne this
  have hfacle : ∀ x ∈ T'.map (fun b => Valued.v (u - b)), x ≤ 1 := by
    intro x hx
    obtain ⟨b, hb, rfl⟩ := Multiset.mem_map.1 hx
    exact (Valuation.map_sub _ _ _).trans (max_le hule (hT'le b hb))
  have hall := eq_one_of_prod_eq_one hfacle hvprod
  have hone : ∀ b ∈ T', Valued.v (u - b) = 1 := fun b hb => hall _ (Multiset.mem_map_of_mem _ hb)
  refine ⟨u, ?_, fun b hb => hone b (Multiset.mem_cons_of_mem hb)⟩
  have := hone 0 (Multiset.mem_cons_self 0 T)
  rwa [sub_zero] at this

theorem exists_circle_point_forall_v_evalAt_le [IsAlgClosed K] (p : RatPair K) (z₀ r : K) (hr : r ≠ 0)
    (hp : ∀ z : K, Valued.v (z - z₀) ≤ Valued.v r → p.den.eval z ≠ 0) :
    ∃ w₀ : K, Valued.v (w₀ - z₀) = Valued.v r ∧
      ∀ z : K, Valued.v (z - z₀) ≤ Valued.v r → Valued.v (p.evalAt z) ≤ Valued.v (p.evalAt w₀) := by
  classical
  have hvr : Valued.v r ≠ 0 := by rwa [ne_eq, map_eq_zero]
  have hvr0 : 0 < Valued.v r := zero_lt_iff.2 hvr

  set R : Multiset K := p.num.roots + p.den.roots with hR
  set T : Multiset K := (R.filter fun α => Valued.v (α - z₀) ≤ Valued.v r).map fun α => (α - z₀) / r with hT
  have hT1 : ∀ b ∈ T, Valued.v b ≤ 1 := by
    intro b hb
    obtain ⟨α, hα, rfl⟩ := Multiset.mem_map.1 hb
    have hα' := (Multiset.mem_filter.1 hα).2
    rw [map_div₀, div_le_one₀ hvr0]
    exact hα'
  obtain ⟨u, hu1, hu⟩ := exists_generic_unit T hT1
  set w₀ : K := z₀ + r * u with hw₀
  have hw₀z : w₀ - z₀ = r * u := by rw [hw₀]; ring
  have hvw₀ : Valued.v (w₀ - z₀) = Valued.v r := by rw [hw₀z, map_mul, hu1, mul_one]
  refine ⟨w₀, hvw₀, fun z hz => ?_⟩

  have hfac : ∀ α ∈ R, Valued.v (z - α) ≤ Valued.v (w₀ - α) ∧
      (Valued.v r < Valued.v (α - z₀) → Valued.v (z - α) = Valued.v (w₀ - α)) := by
    intro α hα
    by_cases hclose : Valued.v (α - z₀) ≤ Valued.v r
    ·
      have hb : (α - z₀) / r ∈ T := Multiset.mem_map_of_mem _ (Multiset.mem_filter.2 ⟨hα, hclose⟩)
      have hw : Valued.v (w₀ - α) = Valued.v r := by
        have : w₀ - α = r * (u - (α - z₀) / r) := by rw [hw₀, mul_sub, mul_div_cancel₀ _ hr]; ring
        rw [this, map_mul, hu _ hb, mul_one]
      refine ⟨?_, fun hfar => absurd hclose (not_le.2 hfar)⟩
      rw [hw]
      have : z - α = (z - z₀) - (α - z₀) := by ring
      rw [this]
      exact (Valuation.map_sub _ _ _).trans (max_le hz hclose)
    · push Not at hclose
      have hw : Valued.v (w₀ - α) = Valued.v (α - z₀) := by
        have : w₀ - α = (w₀ - z₀) - (α - z₀) := by ring
        rw [this]
        exact Valuation.map_sub_eq_of_lt_right _ (hvw₀ ▸ hclose)
      have hzα : Valued.v (z - α) = Valued.v (α - z₀) := by
        have : z - α = (z - z₀) - (α - z₀) := by ring
        rw [this]
        exact Valuation.map_sub_eq_of_lt_right _ (hz.trans_lt hclose)
      exact ⟨by rw [hw, hzα], fun _ => by rw [hw, hzα]⟩

  have hnum : Valued.v (p.num.eval z) ≤ Valued.v (p.num.eval w₀) := by
    rw [(IsAlgClosed.splits p.num).eval_eq_prod_roots z, (IsAlgClosed.splits p.num).eval_eq_prod_roots w₀,
      map_mul, map_mul, map_multiset_prod, map_multiset_prod, Multiset.map_map, Multiset.map_map]
    refine mul_le_mul_right (Multiset.prod_map_le_prod_map _ _ fun α hα => ?_) _
    exact (hfac α (by rw [hR]; exact Multiset.mem_add.2 (Or.inl hα))).1

  have hden : Valued.v (p.den.eval z) = Valued.v (p.den.eval w₀) := by
    rw [(IsAlgClosed.splits p.den).eval_eq_prod_roots z, (IsAlgClosed.splits p.den).eval_eq_prod_roots w₀,
      map_mul, map_mul, map_multiset_prod, map_multiset_prod, Multiset.map_map, Multiset.map_map]
    congr 1
    refine congrArg Multiset.prod (Multiset.map_congr rfl fun β hβ => ?_)
    have hβroot : p.den.eval β = 0 := by
      have hne : p.den ≠ 0 := fun h0 => by
        have := hp z₀ (by simp); rw [h0, eval_zero] at this; exact this rfl
      exact (mem_roots hne).1 hβ
    have hfar : Valued.v r < Valued.v (β - z₀) := by
      by_contra hle
      push Not at hle
      exact hp β hle hβroot
    exact (hfac β (by rw [hR]; exact Multiset.mem_add.2 (Or.inr hβ))).2 hfar
  have hw₀D : Valued.v (w₀ - z₀) ≤ Valued.v r := hvw₀.le
  have hQw : Valued.v (p.den.eval w₀) ≠ 0 := by rw [ne_eq, map_eq_zero]; exact hp w₀ hw₀D
  rw [RatPair.evalAt, RatPair.evalAt, map_div₀, map_div₀, hden]
  exact div_le_div_of_nonneg_right hnum zero_le'

noncomputable def subPair (p q : RatPair K) : RatPair K := RatPair.add p (RatPair.neg q)

theorem subPair_den (p q : RatPair K) : (subPair p q).den = p.den * q.den := rfl

theorem evalAt_subPair {p q : RatPair K} {z : K} (hp : p.den.eval z ≠ 0) (hq : q.den.eval z ≠ 0) :
    (subPair p q).evalAt z = p.evalAt z - q.evalAt z := by
  rw [subPair, RatPair.evalAt_add (q := RatPair.neg q) hp hq, RatPair.evalAt_neg, sub_eq_add_neg]

noncomputable def quotPair (p : RatPair K) (z₀ : K) : RatPair K :=
  ⟨(p.num - C (p.evalAt z₀) * p.den) /ₘ (X - C z₀), p.den⟩

theorem quotPair_den (p : RatPair K) (z₀ : K) : (quotPair p z₀).den = p.den := rfl

theorem sub_mul_evalAt_quotPair (p : RatPair K) {z₀ z : K} (hz₀ : p.den.eval z₀ ≠ 0) (hz : p.den.eval z ≠ 0) :
    (z - z₀) * (quotPair p z₀).evalAt z = p.evalAt z - p.evalAt z₀ := by
  have hroot : IsRoot (p.num - C (p.evalAt z₀) * p.den) z₀ := by
    rw [IsRoot, eval_sub, eval_mul, eval_C, RatPair.evalAt, div_mul_cancel₀ _ hz₀, sub_self]
  have hmul := mul_divByMonic_eq_iff_isRoot.2 hroot
  have heval := congrArg (eval z) hmul
  rw [eval_mul, eval_sub, eval_X, eval_C, eval_sub, eval_mul, eval_C] at heval
  rw [RatPair.evalAt, quotPair, ← mul_div_assoc, heval, RatPair.evalAt, RatPair.evalAt]
  field_simp

theorem exists_v_quotPair_sub_mul_le [IsAlgClosed K] {S : Set K} (p q : RatPair K)
    (hp : p.IsPoleFreeOn S) (hq : q.IsPoleFreeOn S) {z₀ : K} (hz₀ : z₀ ∈ S) {r : K} (hr : r ≠ 0)
    (hD : ∀ z : K, Valued.v (z - z₀) ≤ Valued.v r → z ∈ S) (z : K) (hzS : z ∈ S) :
    ∃ w ∈ S, Valued.v ((quotPair p z₀).evalAt z - (quotPair q z₀).evalAt z) * Valued.v r ≤
      Valued.v ((p.evalAt w - p.evalAt z₀) - (q.evalAt w - q.evalAt z₀)) := by
  have hvr : Valued.v r ≠ 0 := by rwa [ne_eq, map_eq_zero]

  have hid : ∀ w ∈ S, (w - z₀) * ((quotPair p z₀).evalAt w - (quotPair q z₀).evalAt w) =
      (p.evalAt w - p.evalAt z₀) - (q.evalAt w - q.evalAt z₀) := fun w hw => by
    rw [mul_sub, sub_mul_evalAt_quotPair p (hp z₀ hz₀) (hp w hw), sub_mul_evalAt_quotPair q (hq z₀ hz₀) (hq w hw)]
  by_cases hzD : Valued.v (z - z₀) ≤ Valued.v r
  ·
    have hpf : ∀ w : K, Valued.v (w - z₀) ≤ Valued.v r →
        (subPair (quotPair p z₀) (quotPair q z₀)).den.eval w ≠ 0 := fun w hw => by
      rw [subPair_den, quotPair_den, quotPair_den, eval_mul]
      exact mul_ne_zero (hp w (hD w hw)) (hq w (hD w hw))
    obtain ⟨w₀, hw₀, hmax⟩ := exists_circle_point_forall_v_evalAt_le (subPair (quotPair p z₀) (quotPair q z₀))
      z₀ r hr hpf
    have hw₀S : w₀ ∈ S := hD w₀ hw₀.le
    refine ⟨w₀, hw₀S, ?_⟩
    have h1 := hmax z hzD
    rw [evalAt_subPair (p := quotPair p z₀) (q := quotPair q z₀) (hp z hzS) (hq z hzS),
      evalAt_subPair (p := quotPair p z₀) (q := quotPair q z₀) (hp w₀ hw₀S) (hq w₀ hw₀S)] at h1
    rw [← hid w₀ hw₀S, map_mul, hw₀, mul_comm]
    exact mul_le_mul_right h1 _
  ·
    push Not at hzD
    refine ⟨z, hzS, ?_⟩
    rw [← hid z hzS, map_mul, mul_comm]
    exact mul_le_mul_left hzD.le _

section Omega

variable {K₀ : Type} [Field K₀] [Algebra K₀ K] (ϖ : PseudoUniformizer K₀ K)

theorem algebraMap_varpi_ne_zero : algebraMap K₀ K ϖ.ϖ ≠ 0 := fun h => by
  have := ϖ.pos
  rw [h, map_zero] at this
  exact lt_irrefl _ this

theorem mem_affinoid_zero_iff (z : K) :
    z ∈ affinoid ϖ 0 ↔ Valued.v z ≤ 1 ∧
      ∀ a : K₀, Valued.v (algebraMap K₀ K a) ≤ 1 → 1 ≤ Valued.v (z - algebraMap K₀ K a) := by
  simp only [affinoid, pow_zero, Set.mem_setOf_eq]

theorem mem_affinoid_zero_of_v_sub_lt_one {b : K} (hb : b ∈ affinoid ϖ 0) {z : K}
    (hz : Valued.v (z - b) < 1) : z ∈ affinoid ϖ 0 := by
  rw [mem_affinoid_zero_iff] at hb ⊢
  refine ⟨?_, fun a ha => ?_⟩
  · have : z = (z - b) + b := by ring
    rw [this]
    exact (Valuation.map_add _ _ _).trans (max_le hz.le hb.1)
  · have h1 := hb.2 a ha
    have : z - algebraMap K₀ K a = (z - b) + (b - algebraMap K₀ K a) := by ring
    rw [this, Valuation.map_add_eq_of_lt_right _ (hz.trans_le h1)]
    exact h1

theorem add_algebraMap_mem_affinoid_zero {b : K} (hb : b ∈ affinoid ϖ 0) (a : K₀)
    (ha : Valued.v (algebraMap K₀ K a) ≤ 1) : b + algebraMap K₀ K a ∈ affinoid ϖ 0 := by
  rw [mem_affinoid_zero_iff] at hb ⊢
  refine ⟨(Valuation.map_add _ _ _).trans (max_le hb.1 ha), fun a' ha' => ?_⟩
  have : b + algebraMap K₀ K a - algebraMap K₀ K a' = b - algebraMap K₀ K (a' - a) := by
    rw [map_sub]; ring
  rw [this]
  exact hb.2 (a' - a) (by rw [map_sub]; exact (Valuation.map_sub _ _ _).trans (max_le ha' ha))

theorem exists_generic_mem_affinoid_zero [IsAlgClosed K] {b : K} (hb : b ∈ affinoid ϖ 0) (F : Multiset K) :
    ∃ w ∈ affinoid ϖ 0, Valued.v (w - b) = 1 ∧ ∀ γ ∈ F, Valued.v (γ - b) ≤ 1 → Valued.v (w - γ) = 1 := by
  classical
  set n : ℕ := Multiset.card F with hn

  set C : Multiset K := 0 ::ₘ ((F.filter fun γ => Valued.v (γ - b) ≤ 1).map fun γ => γ - b) with hC
  have hC1 : ∀ c ∈ C, Valued.v c ≤ 1 := by
    intro c hc
    rcases Multiset.mem_cons.1 hc with rfl | hc
    · simp
    · obtain ⟨γ, hγ, rfl⟩ := Multiset.mem_map.1 hc
      exact (Multiset.mem_filter.1 hγ).2
  have hCmem : ∀ γ ∈ F, Valued.v (γ - b) ≤ 1 → γ - b ∈ C := fun γ hγ hγb =>
    Multiset.mem_cons_of_mem (Multiset.mem_map_of_mem _ (Multiset.mem_filter.2 ⟨hγ, hγb⟩))
  have h0C : (0 : K) ∈ C := Multiset.mem_cons_self 0 _
  have hCcard : Multiset.card C ≤ n + 1 := by
    rw [hC, Multiset.card_cons, Multiset.card_map]
    exact Nat.succ_le_succ ((Multiset.card_le_card (Multiset.filter_le _ F)).trans hn.ge)

  let P : Finset K₀ → Prop := fun A =>
    (∀ a ∈ A, Valued.v (algebraMap K₀ K a) ≤ 1) ∧
      ∀ a ∈ A, ∀ a' ∈ A, a ≠ a' → 1 ≤ Valued.v (algebraMap K₀ K a - algebraMap K₀ K a')
  by_cases hbig : ∃ A : Finset K₀, P A ∧ n + 2 ≤ A.card
  ·
    obtain ⟨A, ⟨hA1, hAsep⟩, hAcard⟩ := hbig
    have hgood : ∃ a ∈ A, ∀ c ∈ C, 1 ≤ Valued.v (algebraMap K₀ K a - c) := by
      by_contra hall
      push Not at hall
      choose! g hgC hglt using hall
      have hmaps : Set.MapsTo g (A : Set K₀) (C.toFinset : Set K) := fun a ha =>
        Finset.mem_coe.2 (Multiset.mem_toFinset.2 (hgC a ha))
      have hinj : Set.InjOn g (A : Set K₀) := by
        intro a ha a' ha' heq
        by_contra hne
        have h1 := hAsep a ha a' ha' hne
        have : algebraMap K₀ K a - algebraMap K₀ K a' = (algebraMap K₀ K a - g a) - (algebraMap K₀ K a' - g a') := by
          rw [heq]; ring
        rw [this] at h1
        exact not_lt.2 h1 (lt_of_le_of_lt (Valuation.map_sub _ _ _) (max_lt (hglt a ha) (hglt a' ha')))
      have hle := Finset.card_le_card_of_injOn g hmaps hinj
      have hle' : C.toFinset.card ≤ Multiset.card C := Multiset.toFinset_card_le C
      omega
    obtain ⟨a, haA, ha⟩ := hgood
    have hva : Valued.v (algebraMap K₀ K a) = 1 :=
      le_antisymm (hA1 a haA) (by simpa using ha 0 h0C)
    refine ⟨b + algebraMap K₀ K a, add_algebraMap_mem_affinoid_zero ϖ hb a (hA1 a haA), ?_, fun γ hγ hγb => ?_⟩
    · rw [add_sub_cancel_left, hva]
    · have : b + algebraMap K₀ K a - γ = algebraMap K₀ K a - (γ - b) := by ring
      rw [this]
      exact le_antisymm ((Valuation.map_sub _ _ _).trans (max_le (hA1 a haA) hγb)) (ha _ (hCmem γ hγ hγb))
  ·

    have hsmall : ∀ A : Finset K₀, P A → A.card < n + 2 := fun A hA => by
      by_contra hle
      exact hbig ⟨A, hA, not_lt.1 hle⟩
    have hQ : ∃ k : ℕ, ¬ ∃ A : Finset K₀, P A ∧ k ≤ A.card :=
      ⟨n + 2, fun ⟨A, hA, hk⟩ => (hsmall A hA).not_ge hk⟩
    obtain ⟨A, ⟨hA1, hAsep⟩, hmax⟩ : ∃ A : Finset K₀, P A ∧ ¬ ∃ A' : Finset K₀, P A' ∧ A.card + 1 ≤ A'.card := by
      have hk₀ := Nat.find_spec hQ
      have hk₀pos : Nat.find hQ ≠ 0 := by
        intro h0
        rw [h0] at hk₀
        exact hk₀ ⟨∅, ⟨by simp, by simp⟩, Nat.zero_le _⟩
      have hprev : ∃ A : Finset K₀, P A ∧ Nat.find hQ - 1 ≤ A.card := by
        have := Nat.find_min hQ (m := Nat.find hQ - 1) (by omega)
        simpa using this
      obtain ⟨A, hA, hAk⟩ := hprev
      refine ⟨A, hA, fun ⟨A', hA', hA'k⟩ => hk₀ ⟨A', hA', by omega⟩⟩

    have hcov : ∀ a : K₀, Valued.v (algebraMap K₀ K a) ≤ 1 →
        ∃ t ∈ A, Valued.v (algebraMap K₀ K a - algebraMap K₀ K t) < 1 := by
      intro a ha
      by_contra hno
      push Not at hno
      have haA : a ∉ A := fun haA => by
        have := hno a haA
        rw [sub_self, map_zero] at this
        exact not_lt.2 this zero_lt_one
      apply hmax
      refine ⟨insert a A, ⟨?_, ?_⟩, by rw [Finset.card_insert_of_notMem haA]⟩
      · intro x hx
        rcases Finset.mem_insert.1 hx with rfl | hx
        · exact ha
        · exact hA1 x hx
      · intro x hx x' hx' hne
        rcases Finset.mem_insert.1 hx with hxa | hxA
        · rcases Finset.mem_insert.1 hx' with hx'a | hx'A
          · exact absurd (hxa.trans hx'a.symm) hne
          · rw [hxa]; exact hno x' hx'A
        · rcases Finset.mem_insert.1 hx' with hx'a | hx'A
          · rw [hx'a, Valuation.map_sub_swap]; exact hno x hxA
          · exact hAsep x hxA x' hx'A hne

    set T' : Multiset K := (A.val.map fun t => algebraMap K₀ K t - b) + C with hT'
    have hT'1 : ∀ x ∈ T', Valued.v x ≤ 1 := by
      intro x hx
      rcases Multiset.mem_add.1 hx with hx | hx
      · obtain ⟨t, ht, rfl⟩ := Multiset.mem_map.1 hx
        exact (Valuation.map_sub _ _ _).trans (max_le (hA1 t ht) ((mem_affinoid_zero_iff ϖ b).1 hb).1)
      · exact hC1 x hx
    obtain ⟨u, hu1, hu⟩ := exists_generic_unit T' hT'1
    have huA : ∀ t ∈ A, Valued.v (u - (algebraMap K₀ K t - b)) = 1 := fun t ht =>
      hu _ (Multiset.mem_add.2 (Or.inl (Multiset.mem_map_of_mem _ (Finset.mem_def.1 ht))))
    refine ⟨b + u, ?_, by rw [add_sub_cancel_left, hu1], fun γ hγ hγb => ?_⟩
    · rw [mem_affinoid_zero_iff]
      refine ⟨(Valuation.map_add _ _ _).trans (max_le ((mem_affinoid_zero_iff ϖ b).1 hb).1 hu1.le), fun a' ha' => ?_⟩
      obtain ⟨t, ht, hlt⟩ := hcov a' ha'
      have : b + u - algebraMap K₀ K a' = (u - (algebraMap K₀ K t - b)) - (algebraMap K₀ K a' - algebraMap K₀ K t) := by
        ring
      rw [this, Valuation.map_sub_eq_of_lt_left _ (by rw [huA t ht]; exact hlt), huA t ht]
    · have : b + u - γ = u - (γ - b) := by ring
      rw [this]
      exact hu _ (Multiset.mem_add.2 (Or.inr (hCmem γ hγ hγb)))

theorem exists_v_quotPair_le [IsAlgClosed K] (p : RatPair K) (hp : p.IsPoleFreeOn (affinoid ϖ 0))
    {b : K} (hb : b ∈ affinoid ϖ 0) (z : K) (hz : z ∈ affinoid ϖ 0) :
    ∃ w ∈ affinoid ϖ 0, Valued.v ((quotPair p b).evalAt z) ≤ Valued.v (p.evalAt w) := by
  classical
  set q := quotPair p b with hq
  have hden0 : p.den ≠ 0 := fun h0 => by
    have := hp b hb
    rw [h0, eval_zero] at this
    exact this rfl

  have key : ∃ w ∈ affinoid ϖ 0, 1 ≤ Valued.v (w - b) ∧ Valued.v (q.evalAt z) ≤ Valued.v (q.evalAt w) := by
    by_cases hzb : Valued.v (z - b) < 1
    · obtain ⟨w, hwS, hwb, hgen⟩ := exists_generic_mem_affinoid_zero ϖ hb (q.num.roots + q.den.roots)
      refine ⟨w, hwS, hwb.ge, ?_⟩

      have hfac : ∀ α ∈ q.num.roots + q.den.roots, Valued.v (z - α) ≤ Valued.v (w - α) ∧
          (α ∈ q.den.roots → Valued.v (z - α) = Valued.v (w - α)) := by
        intro α hα
        by_cases hclose : Valued.v (α - b) ≤ 1
        · have hw : Valued.v (w - α) = 1 := hgen α hα hclose
          have hzα : Valued.v (z - α) ≤ 1 := by
            have : z - α = (z - b) - (α - b) := by ring
            rw [this]
            exact (Valuation.map_sub _ _ _).trans (max_le hzb.le hclose)
          refine ⟨by rw [hw]; exact hzα, fun hαden => ?_⟩
          rw [hw]
          refine le_antisymm hzα (not_lt.1 fun hlt => ?_)

          have hαS : α ∈ affinoid ϖ 0 :=
            mem_affinoid_zero_of_v_sub_lt_one ϖ hz (by rw [Valuation.map_sub_swap]; exact hlt)
          exact hp α hαS ((mem_roots hden0).1 hαden)
        · push Not at hclose
          have hzα : Valued.v (z - α) = Valued.v (α - b) := by
            have : z - α = (z - b) - (α - b) := by ring
            rw [this]
            exact Valuation.map_sub_eq_of_lt_right _ (hzb.trans hclose)
          have hwα : Valued.v (w - α) = Valued.v (α - b) := by
            have : w - α = (w - b) - (α - b) := by ring
            rw [this]
            exact Valuation.map_sub_eq_of_lt_right _ (hwb ▸ hclose)
          exact ⟨by rw [hzα, hwα], fun _ => by rw [hzα, hwα]⟩
      have hnum : Valued.v (q.num.eval z) ≤ Valued.v (q.num.eval w) := by
        rw [(IsAlgClosed.splits q.num).eval_eq_prod_roots z, (IsAlgClosed.splits q.num).eval_eq_prod_roots w,
          map_mul, map_mul, map_multiset_prod, map_multiset_prod, Multiset.map_map, Multiset.map_map]
        refine mul_le_mul' le_rfl (Multiset.prod_map_le_prod_map _ _ fun α hα => ?_)
        exact (hfac α (Multiset.mem_add.2 (Or.inl hα))).1
      have hden : Valued.v (q.den.eval z) = Valued.v (q.den.eval w) := by
        rw [(IsAlgClosed.splits q.den).eval_eq_prod_roots z, (IsAlgClosed.splits q.den).eval_eq_prod_roots w,
          map_mul, map_mul, map_multiset_prod, map_multiset_prod, Multiset.map_map, Multiset.map_map]
        congr 1
        refine congrArg Multiset.prod (Multiset.map_congr rfl fun β hβ => ?_)
        exact (hfac β (Multiset.mem_add.2 (Or.inr hβ))).2 hβ
      rw [RatPair.evalAt, RatPair.evalAt, map_div₀, map_div₀, hden]
      exact div_le_div_of_nonneg_right hnum zero_le'
    · exact ⟨z, hz, not_lt.1 hzb, le_rfl⟩
  obtain ⟨w, hwS, hwb, hle⟩ := key
  have hwb0 : w - b ≠ 0 := fun h => by
    rw [h, map_zero] at hwb
    exact not_lt.2 hwb zero_lt_one
  have hqw : q.evalAt w = (p.evalAt w - p.evalAt b) / (w - b) := by
    rw [eq_div_iff hwb0, mul_comm]
    exact sub_mul_evalAt_quotPair p (hp b hb) (hp w hwS)
  have hmax : Valued.v (q.evalAt w) ≤ max (Valued.v (p.evalAt w)) (Valued.v (p.evalAt b)) := by
    rw [hqw, map_div₀, div_le_iff₀ (lt_of_lt_of_le zero_lt_one hwb)]
    exact (Valuation.map_sub _ _ _).trans (le_mul_of_one_le_right zero_le' hwb)
  rcases le_total (Valued.v (p.evalAt w)) (Valued.v (p.evalAt b)) with h | h
  · exact ⟨b, hb, hle.trans (hmax.trans (max_le h le_rfl))⟩
  · exact ⟨w, hwS, hle.trans (hmax.trans (max_le le_rfl h))⟩

theorem exists_v_taylor_ratPair_le [IsAlgClosed K] (p : RatPair K) (hp : p.IsPoleFreeOn (affinoid ϖ 0))
    {b : K} (hb : b ∈ affinoid ϖ 0) (z : K) (hz : z ∈ affinoid ϖ 0) :
    ∃ w ∈ affinoid ϖ 0, Valued.v (p.evalAt z - p.evalAt b - (quotPair p b).evalAt b * (z - b)) ≤
      Valued.v (z - b) ^ 2 * Valued.v (p.evalAt w) := by
  set q := quotPair p b with hq
  have hqpf : q.IsPoleFreeOn (affinoid ϖ 0) := fun y hy => hp y hy
  have hid : p.evalAt z - p.evalAt b - q.evalAt b * (z - b) = (z - b) ^ 2 * (quotPair q b).evalAt z := by
    have h1 := sub_mul_evalAt_quotPair p (hp b hb) (hp z hz)
    have h2 := sub_mul_evalAt_quotPair q (hqpf b hb) (hqpf z hz)
    rw [pow_two, mul_assoc, h2]
    linear_combination -h1
  obtain ⟨w₁, hw₁, hle₁⟩ := exists_v_quotPair_le ϖ q hqpf hb z hz
  obtain ⟨w₂, hw₂, hle₂⟩ := exists_v_quotPair_le ϖ p hp hb w₁ hw₁
  refine ⟨w₂, hw₂, ?_⟩
  rw [hid, map_mul, map_pow]
  exact mul_le_mul' le_rfl (hle₁.trans hle₂)

theorem v_le_of_forall_le_max (ϖ : PseudoUniformizer K₀ K) (x : K) (A : Γ₀)
    (h : ∀ y : K, y ≠ 0 → Valued.v x ≤ max A (Valued.v y)) : Valued.v x ≤ A := by
  by_contra hlt
  have hlt' : A < Valued.v x := not_le.1 hlt
  have hx0 : x ≠ 0 := fun h0 => by
    rw [h0, map_zero] at hlt'
    exact not_lt.2 zero_le' hlt'
  have hxe : x * algebraMap K₀ K ϖ.ϖ ≠ 0 := mul_ne_zero hx0 (algebraMap_varpi_ne_zero ϖ)
  have h1 := h _ hxe
  rw [map_mul] at h1
  have h2 : Valued.v x * Valued.v (algebraMap K₀ K ϖ.ϖ) < Valued.v x :=
    mul_lt_of_lt_one_right ((Valuation.pos_iff _).2 hx0) ϖ.lt_one
  exact not_lt.2 h1 (max_lt hlt' h2)

end Omega

end P2mKcDiscTaylor

open P2mKcDiscTaylor in
theorem solution
    (K₀ : Type) [Field K₀] (K : Type) [Field K] [Algebra K₀ K]
    {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀] [CompleteSpace K] [IsAlgClosed K]
    (ϖ : PseudoUniformizer K₀ K)
    (f : ↥(holRing ϖ)) (M : Γ₀)
    (hM : ∀ z : ↥(upperHalfPlane K₀ K), (z : K) ∈ affinoid ϖ 0 → Valued.v ((f : ↥(upperHalfPlane K₀ K) → K) z) ≤ M)
    (b : ↥(upperHalfPlane K₀ K)) (hb : (b : K) ∈ affinoid ϖ 0) :
    ∃ d : K, Valued.v d ≤ M ∧
      ∀ z : ↥(upperHalfPlane K₀ K), Valued.v ((z : K) - (b : K)) < 1 →
        Valued.v ((f : ↥(upperHalfPlane K₀ K) → K) z - (f : ↥(upperHalfPlane K₀ K) → K) b - d * ((z : K) - (b : K))) ≤
          M * Valued.v ((z : K) - (b : K)) ^ 2 := by
  classical
  have hΩ : affinoid ϖ 0 ⊆ upperHalfPlane K₀ K := affinoid_subset_upperHalfPlane ϖ 0
  obtain ⟨p, hpf, -, hlim⟩ := f.2 0
  set F : ↥(affinoid ϖ 0) → K := restrictAffinoid ϖ 0 (f : ↥(upperHalfPlane K₀ K) → K) with hFdef
  have hFapply : ∀ w : ↥(affinoid ϖ 0), F w = (f : ↥(upperHalfPlane K₀ K) → K) ⟨w, hΩ w.2⟩ := fun w => rfl
  have hMS : ∀ w : ↥(affinoid ϖ 0), Valued.v (F w) ≤ M := fun w => hM ⟨w, hΩ w.2⟩ w.2
  rw [tendstoUniformly_iff_vRestrict] at hlim
  have hϖ0 : algebraMap K₀ K ϖ.ϖ ≠ 0 := algebraMap_varpi_ne_zero ϖ

  set dk : ℕ → K := fun k => (quotPair (p k) (b : K)).evalAt (b : K) with hdk

  have hD : ∀ w : K, Valued.v (w - (b : K)) ≤ Valued.v (algebraMap K₀ K ϖ.ϖ) → w ∈ affinoid ϖ 0 := fun w hw =>
    mem_affinoid_zero_of_v_sub_lt_one ϖ hb (lt_of_le_of_lt hw ϖ.lt_one)
  have hcauchy : ∀ γ : (MonoidWithZeroHom.ValueGroup₀ (.ofClass (Valued.v (R := K)) : K →*₀ Γ₀))ˣ, ∃ N : ℕ, ∀ k ≥ N, ∀ j ≥ N,
      vRestrict K (dk k - dk j) < γ := by
    intro γ
    have hwr : vRestrict K (algebraMap K₀ K ϖ.ϖ) ≠ 0 := by rwa [ne_eq, map_eq_zero]
    let c : (MonoidWithZeroHom.ValueGroup₀ (.ofClass (Valued.v (R := K)) : K →*₀ Γ₀))ˣ := Units.mk0 _ hwr
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 (hlim (γ * c))
    refine ⟨N, fun k hk j hj => ?_⟩
    obtain ⟨w, hwS, hle⟩ :=
      exists_v_quotPair_sub_mul_le (p k) (p j) (hpf k) (hpf j) hb hϖ0 hD (b : K) hb
    have h4 : vRestrict K (((p k).evalAt w - (p k).evalAt b) - ((p j).evalAt w - (p j).evalAt b)) < γ * c := by
      have e1 := hN k hk ⟨w, hwS⟩; have e2 := hN k hk ⟨b, hb⟩; have e3 := hN j hj ⟨w, hwS⟩; have e4 := hN j hj ⟨b, hb⟩
      have : ((p k).evalAt w - (p k).evalAt b) - ((p j).evalAt w - (p j).evalAt b) =
          (((p k).evalAt w - F ⟨w, hwS⟩) - ((p j).evalAt w - F ⟨w, hwS⟩)) -
            (((p k).evalAt b - F ⟨b, hb⟩) - ((p j).evalAt b - F ⟨b, hb⟩)) := by ring
      rw [this]
      exact Valuation.map_sub_lt _ (Valuation.map_sub_lt _ e1 e3) (Valuation.map_sub_lt _ e2 e4)
    have hle' : vRestrict K (dk k - dk j) * vRestrict K (algebraMap K₀ K ϖ.ϖ) ≤
        vRestrict K (((p k).evalAt w - (p k).evalAt b) - ((p j).evalAt w - (p j).evalAt b)) := by
      rw [← map_mul, ← v_le_iff_vRestrict_le, map_mul]
      exact hle
    have h5 : vRestrict K (dk k - dk j) * vRestrict K (algebraMap K₀ K ϖ.ϖ) <
        (γ : MonoidWithZeroHom.ValueGroup₀ (.ofClass (Valued.v (R := K)) : K →*₀ Γ₀)) * vRestrict K (algebraMap K₀ K ϖ.ϖ) :=
      lt_of_le_of_lt hle' h4
    exact lt_of_mul_lt_mul_right' h5
  have hCauchy : CauchySeq dk := by
    rw [(Valued.hasBasis_uniformity K Γ₀).cauchySeq_iff]
    intro γ _
    obtain ⟨N, hN⟩ := hcauchy γ
    exact ⟨N, fun m hm n hn => hN n hn m hm⟩
  obtain ⟨d, hd⟩ := cauchySeq_tendsto_of_complete hCauchy

  have hdconv : ∀ y : K, y ≠ 0 → ∃ N : ℕ, ∀ k ≥ N, Valued.v (dk k - d) < Valued.v y := by
    intro y hy
    have hwy : vRestrict K y ≠ 0 := by rwa [ne_eq, map_eq_zero]
    have hmem : {x : K | Valued.v.restrict (x - d) <
        ((Units.mk0 _ hwy : (MonoidWithZeroHom.ValueGroup₀ (.ofClass (Valued.v (R := K)) : K →*₀ Γ₀))ˣ) :
          MonoidWithZeroHom.ValueGroup₀ (.ofClass (Valued.v (R := K)) : K →*₀ Γ₀))} ∈ 𝓝 d :=
      Valued.mem_nhds.2 ⟨Units.mk0 _ hwy, subset_rfl⟩
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 (hd hmem)
    refine ⟨N, fun k hk => ?_⟩
    have h1 : vRestrict K (dk k - d) < vRestrict K y := by simpa using hN k hk
    exact (v_lt_iff_vRestrict_lt K _ _).2 h1
  have hpconv : ∀ y : K, y ≠ 0 → ∃ N : ℕ, ∀ k ≥ N, ∀ w : ↥(affinoid ϖ 0),
      Valued.v ((p k).evalAt w - F w) < Valued.v y := by
    intro y hy
    have hwy : vRestrict K y ≠ 0 := by rwa [ne_eq, map_eq_zero]
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 (hlim (Units.mk0 _ hwy))
    refine ⟨N, fun k hk w => (v_lt_iff_vRestrict_lt K _ _).2 ?_⟩
    simpa using hN k hk w

  have hpM : ∀ (y : K) (k : ℕ), (∀ w : ↥(affinoid ϖ 0), Valued.v ((p k).evalAt w - F w) < Valued.v y) →
      ∀ w ∈ affinoid ϖ 0, Valued.v ((p k).evalAt w) ≤ max M (Valued.v y) := by
    intro y k hk w hwS
    have : (p k).evalAt w = F ⟨w, hwS⟩ + ((p k).evalAt w - F ⟨w, hwS⟩) := by ring
    rw [this]
    exact (Valuation.map_add _ _ _).trans (max_le_max (hMS _) (hk ⟨w, hwS⟩).le)
  refine ⟨d, v_le_of_forall_le_max ϖ d M fun y hy => ?_, fun z hzb => v_le_of_forall_le_max ϖ _ _ fun y hy => ?_⟩
  ·
    obtain ⟨N₁, hN₁⟩ := hdconv y hy
    obtain ⟨N₂, hN₂⟩ := hpconv y hy
    obtain ⟨w, hwS, hle⟩ := exists_v_quotPair_le ϖ (p (max N₁ N₂)) (hpf _) hb (b : K) hb
    have h1 := hpM y (max N₁ N₂) (hN₂ _ (le_max_right _ _)) w hwS
    have : d = dk (max N₁ N₂) - (dk (max N₁ N₂) - d) := by ring
    rw [this]
    exact (Valuation.map_sub _ _ _).trans
      (max_le (hle.trans h1) ((hN₁ _ (le_max_left _ _)).le.trans (le_max_right _ _)))
  ·
    have hzS : (z : K) ∈ affinoid ϖ 0 := mem_affinoid_zero_of_v_sub_lt_one ϖ hb hzb
    obtain ⟨N₁, hN₁⟩ := hdconv y hy
    obtain ⟨N₂, hN₂⟩ := hpconv y hy
    set k := max N₁ N₂ with hk
    obtain ⟨w, hwS, hle⟩ := exists_v_taylor_ratPair_le ϖ (p k) (hpf k) hb (z : K) hzS
    have h1 := hpM y k (hN₂ k (le_max_right _ _)) w hwS
    have hzb1 : Valued.v ((z : K) - (b : K)) ^ 2 ≤ 1 := pow_le_one₀ zero_le' hzb.le
    have h2 : Valued.v ((p k).evalAt z - (p k).evalAt b - dk k * ((z : K) - (b : K))) ≤
        max (M * Valued.v ((z : K) - (b : K)) ^ 2) (Valued.v y) := by
      refine hle.trans ?_
      rcases le_total M (Valued.v y) with hMy | hMy
      · rw [max_eq_right hMy] at h1
        exact (mul_le_mul' hzb1 h1).trans (by rw [one_mul]; exact le_max_right _ _)
      · rw [max_eq_left hMy] at h1
        exact (mul_le_mul' le_rfl h1).trans (by rw [mul_comm]; exact le_max_left _ _)

    have e1 : Valued.v ((f : ↥(upperHalfPlane K₀ K) → K) z - (p k).evalAt z) < Valued.v y := by
      rw [Valuation.map_sub_swap]; exact hN₂ k (le_max_right _ _) ⟨z, hzS⟩
    have e2 : Valued.v ((f : ↥(upperHalfPlane K₀ K) → K) b - (p k).evalAt b) < Valued.v y := by
      rw [Valuation.map_sub_swap]; exact hN₂ k (le_max_right _ _) ⟨b, hb⟩
    have e3 : Valued.v ((d - dk k) * ((z : K) - (b : K))) < Valued.v y := by
      rw [map_mul, Valuation.map_sub_swap]
      exact lt_of_le_of_lt (mul_le_of_le_one_right' hzb.le) (hN₁ k (le_max_left _ _))
    have hsplit : (f : ↥(upperHalfPlane K₀ K) → K) z - (f : ↥(upperHalfPlane K₀ K) → K) b - d * ((z : K) - (b : K)) =
        ((p k).evalAt z - (p k).evalAt b - dk k * ((z : K) - (b : K))) +
          ((((f : ↥(upperHalfPlane K₀ K) → K) z - (p k).evalAt z) -
              ((f : ↥(upperHalfPlane K₀ K) → K) b - (p k).evalAt b)) - (d - dk k) * ((z : K) - (b : K))) := by
      ring
    rw [hsplit]
    refine (Valuation.map_add _ _ _).trans (max_le h2 (le_trans ?_ (le_max_right _ _)))
    exact (Valuation.map_sub_lt _ (Valuation.map_sub_lt _ e1 e2) e3).le

end S_CerednikDrinfeld_Omega_exists_v_sub_sub_mul_le_mul_sq_of_mem_affinoid_zero
end P2MW
export P2MW.S_CerednikDrinfeld_Omega_exists_v_sub_sub_mul_le_mul_sq_of_mem_affinoid_zero (solution)
