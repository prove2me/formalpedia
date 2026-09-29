-- Prove2me | solution 1 for CerednikDrinfeld.Omega.coordSub_dvd_of_apply_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/e8ee845d-3535-51e7-b40c-6392a5888bd6

import Definitions.Def_CerednikDrinfeld_OmegaOrdAt
import Theorems.Thm_CerednikDrinfeld_Omega_exists_forall_v_sub_lt_imp_ne_zero_of_mem_holOn
import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_Omega_coordSub_dvd_of_apply_eq_zero

set_option autoImplicit false

open Filter Polynomial
open scoped Topology
open CerednikDrinfeld.Omega

namespace P2mKcRemovable

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

theorem exists_mem_holOn_eq_sub_mul [CompleteSpace K] [IsAlgClosed K] {S : Set K} {f : ↥S → K}
    (hf : f ∈ holOn K S) (z₀ : ↥S) (hfz₀ : f z₀ = 0) (r : K) (hr : r ≠ 0)
    (hD : ∀ z : K, Valued.v (z - z₀) ≤ Valued.v r → z ∈ S) :
    ∃ g : ↥S → K, g ∈ holOn K S ∧ ∀ z : ↥S, f z = ((z : K) - z₀) * g z := by
  obtain ⟨p, hpf, ⟨b, hb⟩, hlim⟩ := hf
  have hvr : Valued.v r ≠ 0 := by rwa [ne_eq, map_eq_zero]
  have hwr : vRestrict K r ≠ 0 := by rwa [ne_eq, map_eq_zero]

  set q : ℕ → RatPair K := fun k => quotPair (p k) z₀ with hq
  have hqpf : ∀ k, (q k).IsPoleFreeOn S := fun k z hz => hpf k z hz

  have hkey : ∀ k j (z : ↥S), ∃ w : ↥S,
      vRestrict K ((q k).evalAt z - (q j).evalAt z) * vRestrict K r ≤
        vRestrict K (((p k).evalAt w - (p k).evalAt z₀) - ((p j).evalAt w - (p j).evalAt z₀)) := by
    intro k j z
    obtain ⟨w, hwS, hle⟩ := exists_v_quotPair_sub_mul_le (p k) (p j) (hpf k) (hpf j) z₀.2 hr hD z z.2
    refine ⟨⟨w, hwS⟩, ?_⟩
    rw [← map_mul, ← v_le_iff_vRestrict_le, map_mul]
    exact hle
  have hkey1 : ∀ k (z : ↥S), ∃ w : ↥S,
      Valued.v ((q k).evalAt z) * Valued.v r ≤ Valued.v ((p k).evalAt w - (p k).evalAt z₀) := by
    intro k z

    obtain ⟨w, hwS, hle⟩ := exists_v_quotPair_sub_mul_le (p k) (RatPair.const 0) (hpf k)
      (RatPair.isPoleFreeOn_const S 0) z₀.2 hr hD z z.2
    refine ⟨⟨w, hwS⟩, ?_⟩
    have h0 : ∀ y : K, (quotPair (RatPair.const (0 : K)) z₀).evalAt y = 0 := fun y => by
      simp [quotPair, RatPair.evalAt, RatPair.const]
    simpa [h0] using hle

  have hbound : ∀ k (z : ↥S), Valued.v ((q k).evalAt z) ≤ Valued.v (b / r) := by
    intro k z
    obtain ⟨w, hle⟩ := hkey1 k z
    have hnum : Valued.v ((p k).evalAt w - (p k).evalAt z₀) ≤ Valued.v b :=
      (Valuation.map_sub _ _ _).trans (max_le (hb k w) (hb k z₀))
    rw [map_div₀, le_div_iff₀ (zero_lt_iff.2 hvr)]
    exact hle.trans hnum

  rw [tendstoUniformly_iff_vRestrict] at hlim
  have hcauchy : ∀ γ : (MonoidWithZeroHom.ValueGroup₀ (.ofClass (Valued.v (R := K)) : K →*₀ Γ₀))ˣ, ∃ N : ℕ, ∀ k ≥ N, ∀ j ≥ N,
      ∀ z : ↥S, vRestrict K ((q k).evalAt z - (q j).evalAt z) < γ := by
    intro γ
    let c : (MonoidWithZeroHom.ValueGroup₀ (.ofClass (Valued.v (R := K)) : K →*₀ Γ₀))ˣ := Units.mk0 _ hwr
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 (hlim (γ * c))
    refine ⟨N, fun k hk j hj z => ?_⟩
    obtain ⟨w, hle⟩ := hkey k j z
    have h4 : vRestrict K (((p k).evalAt w - (p k).evalAt z₀) - ((p j).evalAt w - (p j).evalAt z₀)) < γ * c := by
      have e1 := hN k hk w; have e2 := hN k hk z₀; have e3 := hN j hj w; have e4 := hN j hj z₀
      rw [hfz₀, sub_zero] at e2 e4
      have : ((p k).evalAt w - (p k).evalAt z₀) - ((p j).evalAt w - (p j).evalAt z₀) =
          (((p k).evalAt w - f w) - ((p j).evalAt w - f w)) - ((p k).evalAt z₀ - (p j).evalAt z₀) := by ring
      rw [this]
      exact Valuation.map_sub_lt _ (Valuation.map_sub_lt _ e1 e3) (Valuation.map_sub_lt _ e2 e4)
    have h5 : vRestrict K ((q k).evalAt z - (q j).evalAt z) * vRestrict K r <
        (γ : MonoidWithZeroHom.ValueGroup₀ (.ofClass (Valued.v (R := K)) : K →*₀ Γ₀)) * vRestrict K r :=
      lt_of_le_of_lt hle h4
    exact lt_of_mul_lt_mul_right' h5

  have hUC : UniformCauchySeqOn (fun k (z : ↥S) => (q k).evalAt z) atTop Set.univ := by
    intro u hu
    obtain ⟨γ, -, hγ⟩ := (Valued.hasBasis_uniformity K Γ₀).mem_iff.1 hu
    obtain ⟨N, hN⟩ := hcauchy γ
    rw [Filter.eventually_iff_exists_mem]
    refine ⟨{m : ℕ × ℕ | N ≤ m.1 ∧ N ≤ m.2}, ?_, fun m hm z _ => hγ ?_⟩
    · rw [Filter.mem_prod_iff]
      exact ⟨Set.Ici N, Filter.mem_atTop N, Set.Ici N, Filter.mem_atTop N, fun m hm => ⟨hm.1, hm.2⟩⟩
    · exact hN m.2 hm.2 m.1 hm.1 z

  have hpt : ∀ z : ↥S, Tendsto (fun k => (p k).evalAt z) atTop (𝓝 (f z)) := by
    intro z
    have hlim' : TendstoUniformly (fun k (z : ↥S) => (p k).evalAt z) f atTop := by
      rw [tendstoUniformly_iff_vRestrict]; exact hlim
    exact hlim'.tendsto_at z
  obtain ⟨ℓ, hℓ⟩ : ∃ ℓ : K, Tendsto (fun k => (q k).evalAt (z₀ : K)) atTop (𝓝 ℓ) :=
    cauchySeq_tendsto_of_complete (hUC.cauchySeq (Set.mem_univ z₀))
  classical
  let g : ↥S → K := fun z => if (z : K) = z₀ then ℓ else f z / ((z : K) - z₀)
  have hgpt : ∀ z : ↥S, Tendsto (fun k => (q k).evalAt z) atTop (𝓝 (g z)) := by
    intro z
    by_cases hz : (z : K) = z₀
    · have hzz : z = z₀ := Subtype.ext hz
      subst hzz
      simpa [g] using hℓ
    · simp only [g, hz, if_false]
      have hne : (z : K) - z₀ ≠ 0 := sub_ne_zero.2 hz
      have hquot : ∀ k, (q k).evalAt z = ((p k).evalAt z - (p k).evalAt z₀) / ((z : K) - z₀) := fun k => by
        rw [eq_div_iff hne, mul_comm]
        exact sub_mul_evalAt_quotPair (p k) (hpf k z₀ z₀.2) (hpf k z z.2)
      simp_rw [hquot]
      have h1 : Tendsto (fun k => (p k).evalAt z - (p k).evalAt z₀) atTop (𝓝 (f z - f z₀)) :=
        (hpt z).sub (hpt z₀)
      rw [hfz₀, sub_zero] at h1
      exact h1.div_const _
  have hgunif : TendstoUniformly (fun k (z : ↥S) => (q k).evalAt z) g atTop := by
    rw [← tendstoUniformlyOn_univ]
    exact hUC.tendstoUniformlyOn_of_tendsto fun z _ => hgpt z
  refine ⟨g, ⟨q, hqpf, ⟨b / r, hbound⟩, hgunif⟩, fun z => ?_⟩
  by_cases hz : (z : K) = z₀
  · have hzz : z = z₀ := Subtype.ext hz
    rw [hzz, hfz₀, sub_self, zero_mul]
  · simp only [g, hz, if_false]
    rw [mul_div_cancel₀ _ (sub_ne_zero.2 hz)]

theorem isHolOn_restrict {S T : Set K} {f : ↥S → K} (hf : IsHolOn K S f) (hTS : T ⊆ S) :
    IsHolOn K T (f ∘ Set.inclusion hTS) := by
  obtain ⟨r, hr, ⟨b, hb⟩, hlim⟩ := hf
  refine ⟨r, fun k z hz => hr k z (hTS hz), ⟨b, fun k z => hb k (Set.inclusion hTS z)⟩, ?_⟩
  rw [tendstoUniformly_iff_vRestrict] at hlim ⊢
  intro γ
  filter_upwards [hlim γ] with k hk z
  exact hk (Set.inclusion hTS z)

section Omega

variable {K₀ : Type} [Field K₀] [Algebra K₀ K] (ϖ : PseudoUniformizer K₀ K)

theorem algebraMap_varpi_ne_zero : algebraMap K₀ K ϖ.ϖ ≠ 0 := fun h => by
  have := ϖ.pos
  rw [h, map_zero] at this
  exact lt_irrefl _ this

theorem pow_succ_lt_pow (n : ℕ) :
    Valued.v (algebraMap K₀ K ϖ.ϖ) ^ (n + 1) < Valued.v (algebraMap K₀ K ϖ.ϖ) ^ n := by
  rw [pow_succ]
  exact mul_lt_of_lt_one_right (pow_pos ϖ.pos n) ϖ.lt_one

theorem mem_affinoid_of_v_sub_le {n : ℕ} {z : K} (hz : z ∈ affinoid ϖ n) {w : K}
    (hw : Valued.v (w - z) ≤ Valued.v (algebraMap K₀ K ϖ.ϖ) ^ (n + 1)) : w ∈ affinoid ϖ n := by
  have hp0 : 0 < Valued.v (algebraMap K₀ K ϖ.ϖ) := ϖ.pos
  have hp1 : Valued.v (algebraMap K₀ K ϖ.ϖ) < 1 := ϖ.lt_one
  rw [mem_affinoid_iff'] at hz ⊢
  obtain ⟨hz1, hz2⟩ := hz
  have hwz : Valued.v (w - z) < Valued.v (algebraMap K₀ K ϖ.ϖ) ^ n := lt_of_le_of_lt hw (pow_succ_lt_pow ϖ n)
  constructor
  · have h1 : Valued.v (algebraMap K₀ K ϖ.ϖ) ^ n ≤ 1 := pow_le_one₀ zero_le' hp1.le
    have h2 : (1 : Γ₀) ≤ (Valued.v (algebraMap K₀ K ϖ.ϖ))⁻¹ ^ n := one_le_pow₀ ((one_le_inv₀ hp0).2 hp1.le)
    have : w = (w - z) + z := by ring
    rw [this]
    exact (Valuation.map_add _ _ _).trans (max_le (hwz.le.trans (h1.trans h2)) hz1)
  · intro a
    have hza := hz2 a
    have hlt' : Valued.v (w - z) < Valued.v (z - algebraMap K₀ K a) := lt_of_lt_of_le hwz hza
    have : w - algebraMap K₀ K a = (w - z) + (z - algebraMap K₀ K a) := by ring
    rw [this, Valuation.map_add_eq_of_lt_right _ hlt']
    exact hza

theorem exists_ne_and_v_sub_lt (z c : K) (hc : c ≠ 0) (n : ℕ) :
    ∃ w : K, w ≠ z ∧ Valued.v (w - z) < Valued.v c ∧
      Valued.v (w - z) ≤ Valued.v (algebraMap K₀ K ϖ.ϖ) ^ (n + 1) := by
  have hϖ0 := algebraMap_varpi_ne_zero ϖ
  have hvc : 0 < Valued.v c := zero_lt_iff.2 (by rwa [ne_eq, map_eq_zero])
  by_cases h : Valued.v c ≤ Valued.v (algebraMap K₀ K ϖ.ϖ) ^ (n + 1)
  · refine ⟨z + c * algebraMap K₀ K ϖ.ϖ, ?_, ?_, ?_⟩
    · intro h0
      have : c * algebraMap K₀ K ϖ.ϖ = 0 := by
        have := congrArg (fun x => x - z) h0
        simpa using this
      exact (mul_ne_zero hc hϖ0) this
    · rw [add_sub_cancel_left, map_mul]
      exact mul_lt_of_lt_one_right hvc ϖ.lt_one
    · rw [add_sub_cancel_left, map_mul]
      exact (mul_le_of_le_one_right' ϖ.lt_one.le).trans h
  · push Not at h
    refine ⟨z + algebraMap K₀ K ϖ.ϖ ^ (n + 2), ?_, ?_, ?_⟩
    · intro h0
      have : algebraMap K₀ K ϖ.ϖ ^ (n + 2) = 0 := by
        have := congrArg (fun x => x - z) h0
        simpa using this
      exact pow_ne_zero _ hϖ0 this
    · rw [add_sub_cancel_left, map_pow]
      exact (pow_succ_lt_pow ϖ (n + 1)).trans h
    · rw [add_sub_cancel_left, map_pow]
      exact (pow_succ_lt_pow ϖ (n + 1)).le

theorem exists_div_level [CompleteSpace K] [IsAlgClosed K] (H : ↥(holRing ϖ)) (z : ↥(upperHalfPlane K₀ K))
    (hz : (H : ↥(upperHalfPlane K₀ K) → K) z = 0) {N : ℕ} (hzN : (z : K) ∈ affinoid ϖ N) (n : ℕ) (hn : N ≤ n) :
    ∃ g : ↥(affinoid ϖ n) → K, g ∈ holOn K (affinoid ϖ n) ∧
      ∀ w : ↥(affinoid ϖ n), (H : ↥(upperHalfPlane K₀ K) → K) ⟨w, affinoid_subset_upperHalfPlane ϖ n w.2⟩ =
        ((w : K) - z) * g w := by
  have hzn : (z : K) ∈ affinoid ϖ n := affinoid_mono ϖ hn hzN
  have hr : algebraMap K₀ K ϖ.ϖ ^ (N + 1) ≠ 0 := pow_ne_zero _ (algebraMap_varpi_ne_zero ϖ)
  have hD : ∀ w : K, Valued.v (w - ((⟨(z : K), hzn⟩ : ↥(affinoid ϖ n)) : K)) ≤
      Valued.v (algebraMap K₀ K ϖ.ϖ ^ (N + 1)) → w ∈ affinoid ϖ n := fun w hw => by
    rw [map_pow] at hw
    exact affinoid_mono ϖ hn (mem_affinoid_of_v_sub_le ϖ hzN hw)
  obtain ⟨g, hg, hgeq⟩ := exists_mem_holOn_eq_sub_mul (S := affinoid ϖ n) (f := restrictAffinoid ϖ n H) (H.2 n)
    ⟨z, hzn⟩ hz _ hr hD
  exact ⟨g, hg, fun w => hgeq w⟩

theorem exists_eq_coordSub_mul [CompleteSpace K] [IsAlgClosed K] (hex : IsExhausted ϖ)
    (H : ↥(holRing ϖ)) (z : ↥(upperHalfPlane K₀ K)) (hz : (H : ↥(upperHalfPlane K₀ K) → K) z = 0) :
    ∃ Q : ↥(holRing ϖ), H = coordSub ϖ z * Q := by
  classical
  obtain ⟨N, hzN⟩ := hex z z.2
  obtain ⟨gN, hgN, hgNeq⟩ := exists_div_level ϖ H z hz hzN N le_rfl

  have hcons : ∀ (n : ℕ) (hn : N ≤ n) (g : ↥(affinoid ϖ n) → K), g ∈ holOn K (affinoid ϖ n) →
      (∀ w : ↥(affinoid ϖ n), (H : ↥(upperHalfPlane K₀ K) → K) ⟨w, affinoid_subset_upperHalfPlane ϖ n w.2⟩ =
        ((w : K) - z) * g w) →
      ∀ w : ↥(affinoid ϖ N), g (Set.inclusion (affinoid_mono ϖ hn) w) = gN w := by
    intro n hn g hg hgeq
    have hsub : affinoid ϖ N ⊆ affinoid ϖ n := affinoid_mono ϖ hn
    set d : ↥(affinoid ϖ N) → K := fun w => g (Set.inclusion hsub w) - gN w with hd
    have hdmem : d ∈ holOn K (affinoid ϖ N) :=
      (holOn K (affinoid ϖ N)).sub_mem (isHolOn_restrict hg hsub) hgN
    have hd0 : ∀ w : ↥(affinoid ϖ N), (w : K) ≠ z → d w = 0 := by
      intro w hw
      have h1 := hgeq (Set.inclusion hsub w)
      have h2 := hgNeq w
      have h12 : ((w : K) - z) * (g (Set.inclusion hsub w) - gN w) = 0 := by
        rw [mul_sub, ← h2]
        exact sub_eq_zero.2 h1.symm
      exact (mul_eq_zero.1 h12).resolve_left (sub_ne_zero.2 hw)
    suffices hall : ∀ w : ↥(affinoid ϖ N), d w = 0 by
      intro w
      exact sub_eq_zero.1 (hall w)
    intro w
    by_cases hwz : (w : K) = z
    · by_contra hne
      obtain ⟨c, hc, hcnv⟩ :=
        CerednikDrinfeld.Omega.exists_forall_v_sub_lt_imp_ne_zero_of_mem_holOn K hdmem w hne
      obtain ⟨w', hw'ne, hw'lt, hw'le⟩ := exists_ne_and_v_sub_lt ϖ (w : K) c hc N
      have hw'N : w' ∈ affinoid ϖ N := mem_affinoid_of_v_sub_le ϖ w.2 hw'le
      have h1 := hcnv ⟨w', hw'N⟩ hw'lt
      have h2 := hd0 ⟨w', hw'N⟩ (by rw [← hwz]; exact hw'ne)
      exact h1 h2
    · exact hd0 w hwz

  let Q : ↥(upperHalfPlane K₀ K) → K := fun w =>
    if h : (w : K) ∈ affinoid ϖ N then gN ⟨w, h⟩ else (H : ↥(upperHalfPlane K₀ K) → K) w / ((w : K) - z)
  have hQmem : Q ∈ holRing ϖ := by
    intro n
    rcases le_or_gt n N with hn | hn
    · have hsub : affinoid ϖ n ⊆ affinoid ϖ N := affinoid_mono ϖ hn
      have heq : restrictAffinoid ϖ n Q = gN ∘ Set.inclusion hsub := by
        funext w
        show Q ⟨w, _⟩ = gN ⟨w, hsub w.2⟩
        simp only [Q, dif_pos (hsub w.2)]
      rw [heq]
      exact isHolOn_restrict hgN hsub
    · obtain ⟨g, hg, hgeq⟩ := exists_div_level ϖ H z hz hzN n hn.le
      have heq : restrictAffinoid ϖ n Q = g := by
        funext w
        show Q ⟨w, _⟩ = g w
        by_cases hw : (w : K) ∈ affinoid ϖ N
        · simp only [Q, dif_pos hw]
          exact (hcons n hn.le g hg hgeq ⟨w, hw⟩).symm
        · have hwz : (w : K) ≠ z := fun h => hw (h ▸ hzN)
          simp only [Q, dif_neg hw]
          rw [div_eq_iff (sub_ne_zero.2 hwz), mul_comm]
          exact hgeq w
      rw [heq]
      exact hg
  refine ⟨⟨Q, hQmem⟩, Subtype.ext (funext fun w => ?_)⟩
  show (H : ↥(upperHalfPlane K₀ K) → K) w = ((w : K) - z) * Q w
  by_cases hw : (w : K) ∈ affinoid ϖ N
  · simp only [Q, dif_pos hw]
    exact hgNeq ⟨w, hw⟩
  · have hwz : (w : K) ≠ z := fun h => hw (h ▸ hzN)
    simp only [Q, dif_neg hw]
    rw [mul_div_cancel₀ _ (sub_ne_zero.2 hwz)]

end Omega

end P2mKcRemovable

open P2mKcRemovable in
theorem solution
    (K₀ : Type) [Field K₀] (K : Type) [Field K] [Algebra K₀ K]
    {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀] [CompleteSpace K] [IsAlgClosed K]
    (ϖ : PseudoUniformizer K₀ K)
    (hrk : ∀ x y : K, Valued.v x < 1 → y ≠ 0 → ∃ n : ℕ, Valued.v x ^ n ≤ Valued.v y)
    (hex : IsExhausted ϖ)
    (F : ↥(holRing ϖ)) (z : ↥(upperHalfPlane K₀ K))
    (hF : (F : ↥(upperHalfPlane K₀ K) → K) z = 0) :
    coordSub ϖ z ∣ F := by
  obtain ⟨Q, hQ⟩ := exists_eq_coordSub_mul ϖ hex F z hF
  exact ⟨Q, hQ⟩

end S_CerednikDrinfeld_Omega_coordSub_dvd_of_apply_eq_zero
end P2MW
export P2MW.S_CerednikDrinfeld_Omega_coordSub_dvd_of_apply_eq_zero (solution)
