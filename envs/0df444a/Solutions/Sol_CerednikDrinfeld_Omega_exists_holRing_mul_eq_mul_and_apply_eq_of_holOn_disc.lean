-- Prove2me | solution 1 for CerednikDrinfeld.Omega.exists_holRing_mul_eq_mul_and_apply_eq_of_holOn_disc
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/bf19503b-c5c4-536c-b506-b616683d1604

import Mathlib
import Definitions.Def_CerednikDrinfeld_DrinfeldHolomorphic
import Definitions.Def_CerednikDrinfeld_OmegaOrdAt
import Theorems.Thm_CerednikDrinfeld_Omega_exists_eq_coordSub_pow_ordAt_mul_and_apply_ne_zero
import Theorems.Thm_CerednikDrinfeld_Omega_restrict_mem_holOn_of_subset
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_Omega_exists_holRing_mul_eq_mul_and_apply_eq_of_holOn_disc

set_option autoImplicit false

open Filter Topology CerednikDrinfeld CerednikDrinfeld.Omega

noncomputable section

namespace MeroValueBody

variable {K₀ : Type} [Field K₀] {K : Type} [Field K] [Algebra K₀ K]
variable {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]

theorem continuous_evalAt {S : Set K} (r : RatPair K) (hr : r.IsPoleFreeOn S) :
    Continuous (fun z : ↥S => r.evalAt (z : K)) := by
  show Continuous (fun z : ↥S => r.num.eval (z : K) / r.den.eval (z : K))
  exact ((r.num.continuous).comp continuous_subtype_val).div ((r.den.continuous).comp continuous_subtype_val)
    (fun z => hr z z.2)

theorem continuous_of_mem_holOn {S : Set K} {f : ↥S → K} (hf : f ∈ holOn K S) : Continuous f := by
  rw [mem_holOn_iff] at hf
  obtain ⟨r, hpf, -, hconv⟩ := hf
  exact hconv.continuous (Filter.Eventually.of_forall (fun k => continuous_evalAt (r k) (hpf k))).frequently

section Disc

variable (ϖ : PseudoUniformizer K₀ K)
  (hrk : ∀ x y : K, Valued.v x < 1 → y ≠ 0 → ∃ n : ℕ, Valued.v x ^ n ≤ Valued.v y)

theorem algebraMap_ne_zero : algebraMap K₀ K ϖ.ϖ ≠ 0 := fun h => by
  have := ϖ.pos; rw [h, map_zero] at this; exact lt_irrefl _ this

include hrk in

theorem tendsto_pow_zero (M : ℕ) : Tendsto (fun k : ℕ => algebraMap K₀ K ϖ.ϖ ^ (M + k)) atTop (𝓝 0) := by
  rw [(Valued.hasBasis_nhds_zero K Γ₀).tendsto_right_iff]
  intro γ _
  obtain ⟨y, hy⟩ := MonoidWithZeroHom.ValueGroup₀.restrict₀_surjective (Valued.v (R := K)).toMonoidWithZeroHom γ.1
  have hy0 : y ≠ 0 := fun h0 => by
    rw [h0, map_zero] at hy
    exact γ.ne_zero hy.symm
  obtain ⟨n, hn⟩ := hrk (algebraMap K₀ K ϖ.ϖ) y ϖ.lt_one hy0
  refine Filter.eventually_atTop.2 ⟨n + 1, fun k hk => ?_⟩
  show (Valued.v (R := K)).restrict (algebraMap K₀ K ϖ.ϖ ^ (M + k)) < γ.1
  rw [← hy]
  show vRestrict K _ < vRestrict K y
  rw [← v_lt_iff_vRestrict_lt]
  have hp1 : Valued.v (algebraMap K₀ K ϖ.ϖ) ≤ 1 := ϖ.lt_one.le
  calc Valued.v (algebraMap K₀ K ϖ.ϖ ^ (M + k)) = Valued.v (algebraMap K₀ K ϖ.ϖ) ^ (M + k) := map_pow _ _ _
    _ ≤ Valued.v (algebraMap K₀ K ϖ.ϖ) ^ (n + 1) := pow_le_pow_right_of_le_one' hp1 (by omega)
    _ = Valued.v (algebraMap K₀ K ϖ.ϖ) ^ n * Valued.v (algebraMap K₀ K ϖ.ϖ) := pow_succ _ _
    _ < Valued.v (algebraMap K₀ K ϖ.ϖ) ^ n * 1 := by
        apply mul_lt_mul_of_pos_left ϖ.lt_one
        exact pow_pos ϖ.pos n
    _ = Valued.v (algebraMap K₀ K ϖ.ϖ) ^ n := mul_one _
    _ ≤ Valued.v y := hn

theorem pow_injective {i j : ℕ} (h : algebraMap K₀ K ϖ.ϖ ^ i = algebraMap K₀ K ϖ.ϖ ^ j) : i = j := by
  by_contra hij
  wlog hlt : i < j generalizing i j
  · exact this h.symm (Ne.symm hij) (lt_of_le_of_ne (not_lt.mp hlt) (Ne.symm hij))
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_lt hlt
  have hπ := algebraMap_ne_zero ϖ
  have h1 : algebraMap K₀ K ϖ.ϖ ^ (d + 1) = 1 := by
    have : algebraMap K₀ K ϖ.ϖ ^ i * algebraMap K₀ K ϖ.ϖ ^ (d + 1) = algebraMap K₀ K ϖ.ϖ ^ i * 1 := by
      rw [mul_one, ← pow_add, show i + (d + 1) = i + d + 1 by omega, ← h]
    exact mul_left_cancel₀ (pow_ne_zero i hπ) this
  have h2 : Valued.v (algebraMap K₀ K ϖ.ϖ ^ (d + 1)) < 1 := by
    rw [map_pow]
    calc Valued.v (algebraMap K₀ K ϖ.ϖ) ^ (d + 1) ≤ Valued.v (algebraMap K₀ K ϖ.ϖ) ^ 1 :=
          pow_le_pow_right_of_le_one' ϖ.lt_one.le (by omega)
      _ = Valued.v (algebraMap K₀ K ϖ.ϖ) := pow_one _
      _ < 1 := ϖ.lt_one
  rw [h1, map_one] at h2
  exact lt_irrefl _ h2

variable (c : K) (N : ℕ)

abbrev disc : Set K := {w : K | Valued.v (w - c) ≤ Valued.v (algebraMap K₀ K ϖ.ϖ) ^ N}

theorem add_pow_mem_disc {w : K} (hw : w ∈ disc ϖ c N) (k : ℕ) : w + algebraMap K₀ K ϖ.ϖ ^ (N + k) ∈ disc ϖ c N := by
  show Valued.v (w + algebraMap K₀ K ϖ.ϖ ^ (N + k) - c) ≤ _
  have h1 : Valued.v (algebraMap K₀ K ϖ.ϖ ^ (N + k)) ≤ Valued.v (algebraMap K₀ K ϖ.ϖ) ^ N := by
    rw [map_pow]; exact pow_le_pow_right_of_le_one' ϖ.lt_one.le (Nat.le_add_right N k)
  rw [show w + algebraMap K₀ K ϖ.ϖ ^ (N + k) - c = (w - c) + algebraMap K₀ K ϖ.ϖ ^ (N + k) by ring]
  exact (Valuation.map_add _ _ _).trans (max_le hw h1)

include hrk in

theorem eq_of_eqOn_compl_finite {f g : ↥(disc ϖ c N) → K} (hf : Continuous f) (hg : Continuous g)
    (Z : Set ↥(disc ϖ c N)) (hZ : Z.Finite) (h : ∀ w : ↥(disc ϖ c N), w ∉ Z → f w = g w) (w₀ : ↥(disc ϖ c N)) :
    f w₀ = g w₀ := by
  let u : ℕ → ↥(disc ϖ c N) := fun k => ⟨(w₀ : K) + algebraMap K₀ K ϖ.ϖ ^ (N + k), add_pow_mem_disc ϖ c N w₀.2 k⟩
  have hu_inj : Function.Injective u := by
    intro i j hij
    have h1 : (w₀ : K) + algebraMap K₀ K ϖ.ϖ ^ (N + i) = (w₀ : K) + algebraMap K₀ K ϖ.ϖ ^ (N + j) :=
      congrArg Subtype.val hij
    have := pow_injective ϖ (add_left_cancel h1)
    omega
  have hfin : (u ⁻¹' Z).Finite := hZ.preimage (hu_inj.injOn)
  obtain ⟨k₀, hk₀⟩ := hfin.bddAbove
  have hev : ∀ᶠ k in atTop, f (u k) = g (u k) := by
    refine Filter.eventually_atTop.2 ⟨k₀ + 1, fun k hk => h (u k) (fun hmem => ?_)⟩
    have := hk₀ hmem
    omega
  have hu : Tendsto u atTop (𝓝 w₀) := by
    rw [tendsto_subtype_rng]
    show Tendsto (fun k => (w₀ : K) + algebraMap K₀ K ϖ.ϖ ^ (N + k)) atTop (𝓝 (w₀ : K))
    have := (tendsto_const_nhds (x := (w₀ : K)) (f := (atTop : Filter ℕ))).add (tendsto_pow_zero ϖ hrk N)
    rwa [add_zero] at this
  exact tendsto_nhds_unique_of_eventuallyEq (hf.continuousAt.tendsto.comp hu) (hg.continuousAt.tendsto.comp hu) hev

end Disc

end MeroValueBody

open MeroValueBody in
theorem solution
    (K₀ : Type) [Field K₀] (K : Type) [Field K] [Algebra K₀ K] [DecidableEq K]
    {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]
    (hrk : ∀ x y : K, Valued.v x < 1 → y ≠ 0 → ∃ n : ℕ, Valued.v x ^ n ≤ Valued.v y)
    [CompleteSpace K] [IsAlgClosed K]
    (ϖ : Omega.PseudoUniformizer K₀ K) (hex : Omega.IsExhausted ϖ)
    (hfin : ∀ n : ℕ, ∃ T : Finset K₀, ∀ a : K₀, Valued.v (algebraMap K₀ K a) ≤ (Valued.v (algebraMap K₀ K ϖ.ϖ))⁻¹ ^ n →
      ∃ t ∈ T, Valued.v (algebraMap K₀ K a - algebraMap K₀ K t) < (Valued.v (algebraMap K₀ K ϖ.ϖ)) ^ n)
    (A B : ↥(Omega.holRing ϖ)) (hB : B ≠ 0) (z : ↥(Omega.upperHalfPlane K₀ K)) (N : ℕ)
    (hD : {w : K | Valued.v (w - (z : K)) ≤ Valued.v (algebraMap K₀ K ϖ.ϖ) ^ N} ⊆ Omega.upperHalfPlane K₀ K)
    (a b : ↥{w : K | Valued.v (w - (z : K)) ≤ Valued.v (algebraMap K₀ K ϖ.ϖ) ^ N} → K)
    (ha : a ∈ Omega.holOn K {w : K | Valued.v (w - (z : K)) ≤ Valued.v (algebraMap K₀ K ϖ.ϖ) ^ N}) (hb : b ∈ Omega.holOn K {w : K | Valued.v (w - (z : K)) ≤ Valued.v (algebraMap K₀ K ϖ.ϖ) ^ N})
    (hbz : ∀ w : ↥{w : K | Valued.v (w - (z : K)) ≤ Valued.v (algebraMap K₀ K ϖ.ϖ) ^ N}, (w : K) = (z : K) → b w ≠ 0)
    (heq : ∃ Z : Set ↥{w : K | Valued.v (w - (z : K)) ≤ Valued.v (algebraMap K₀ K ϖ.ϖ) ^ N}, Z.Finite ∧ ∀ w : ↥{w : K | Valued.v (w - (z : K)) ≤ Valued.v (algebraMap K₀ K ϖ.ϖ) ^ N}, w ∉ Z →
      (B : ↥(Omega.upperHalfPlane K₀ K) → K) ⟨(w : K), hD w.2⟩ * a w = (A : ↥(Omega.upperHalfPlane K₀ K) → K) ⟨(w : K), hD w.2⟩ * b w) :
    ∃ G H : ↥(Omega.holRing ϖ), (H : ↥(Omega.upperHalfPlane K₀ K) → K) z ≠ 0 ∧ A * H = B * G ∧
      ∀ w : ↥{w : K | Valued.v (w - (z : K)) ≤ Valued.v (algebraMap K₀ K ϖ.ϖ) ^ N}, (w : K) = (z : K) →
        (G : ↥(Omega.upperHalfPlane K₀ K) → K) z * b w = (H : ↥(Omega.upperHalfPlane K₀ K) → K) z * a w := by
  classical

  obtain ⟨n₀, hn₀⟩ := hex (z : K) z.2
  have hz' := (mem_affinoid_iff' ϖ n₀ (z : K)).1 hn₀
  have hDaff : disc ϖ (z : K) N ⊆ affinoid ϖ n₀ := by
    intro w hw
    rw [mem_affinoid_iff']
    have hw' : Valued.v (w - (z : K)) ≤ Valued.v (algebraMap K₀ K ϖ.ϖ) ^ N := hw
    have hp1 : Valued.v (algebraMap K₀ K ϖ.ϖ) ≤ 1 := ϖ.lt_one.le
    have hinv : 1 ≤ (Valued.v (algebraMap K₀ K ϖ.ϖ))⁻¹ := (one_le_inv₀ ϖ.pos).2 hp1
    constructor
    · rw [show w = (w - (z : K)) + (z : K) by ring]
      refine (Valuation.map_add _ _ _).trans (max_le (hw'.trans ?_) hz'.1)
      exact (pow_le_one₀ zero_le' hp1).trans (one_le_pow₀ hinv)
    · intro t
      rcases lt_or_ge (Valued.v (w - (z : K))) (Valued.v ((z : K) - algebraMap K₀ K t)) with hlt | hge
      · rw [show w - algebraMap K₀ K t = (w - (z : K)) + ((z : K) - algebraMap K₀ K t) by ring,
          Valuation.map_add_eq_of_lt_right _ hlt]
        exact hz'.2 t
      · exfalso
        have hmem : algebraMap K₀ K t ∈ disc ϖ (z : K) N := by
          show Valued.v (algebraMap K₀ K t - (z : K)) ≤ _
          rw [← Valuation.map_neg, neg_sub]
          exact hge.trans hw'
        exact ((mem_upperHalfPlane_iff K₀ _).1 (hD hmem)) t rfl

  have hcontR : ∀ F : ↥(Omega.holRing ϖ),
      Continuous (fun w : ↥(disc ϖ (z : K) N) => (F : ↥(Omega.upperHalfPlane K₀ K) → K) ⟨(w : K), hD w.2⟩) := by
    intro F
    have h1 : restrictAffinoid ϖ n₀ (F : ↥(Omega.upperHalfPlane K₀ K) → K) ∈ holOn K (affinoid ϖ n₀) := F.2 n₀
    exact continuous_of_mem_holOn (CerednikDrinfeld.Omega.restrict_mem_holOn_of_subset K hDaff h1)
  have hca : Continuous a := continuous_of_mem_holOn ha
  have hcb : Continuous b := continuous_of_mem_holOn hb

  obtain ⟨Z, hZ, hZeq⟩ := heq
  have hall : ∀ w : ↥(disc ϖ (z : K) N),
      (B : ↥(Omega.upperHalfPlane K₀ K) → K) ⟨(w : K), hD w.2⟩ * a w =
        (A : ↥(Omega.upperHalfPlane K₀ K) → K) ⟨(w : K), hD w.2⟩ * b w :=
    eq_of_eqOn_compl_finite ϖ hrk (z : K) N ((hcontR B).mul hca) ((hcontR A).mul hcb) Z hZ hZeq

  have hzD : (z : K) ∈ disc ϖ (z : K) N := by
    show Valued.v ((z : K) - (z : K)) ≤ _
    rw [sub_self, map_zero]; exact zero_le'

  let Zc : Set ↥(disc ϖ (z : K) N) := {w | (w : K) = (z : K)}
  have hZc : Zc.Finite := by
    refine Set.Finite.subset (Set.finite_singleton (⟨(z : K), hzD⟩ : ↥(disc ϖ (z : K) N))) ?_
    intro w hw
    exact Subtype.ext hw
  have hzeq : ∀ w : ↥(disc ϖ (z : K) N), (w : K) = (z : K) →
      (⟨(w : K), hD w.2⟩ : ↥(Omega.upperHalfPlane K₀ K)) = z := fun w hw => Subtype.ext hw

  obtain ⟨B₁, hB₁, hB₁z⟩ :=
    CerednikDrinfeld.Omega.exists_eq_coordSub_pow_ordAt_mul_and_apply_ne_zero K₀ K hrk ϖ hex hfin B hB z
  set n := Omega.ordAt ϖ B z with hn

  have hzz : (⟨(z : K), hD hzD⟩ : ↥(Omega.upperHalfPlane K₀ K)) = z := Subtype.ext rfl
  by_cases hA : A = 0
  · refine ⟨0, 1, ?_, by rw [hA, mul_zero, zero_mul], fun w hw => ?_⟩
    · show (1 : K) ≠ 0
      exact one_ne_zero
    · obtain rfl : w = ⟨(z : K), hzD⟩ := Subtype.ext hw

      have hoff : ∀ w' : ↥(disc ϖ (z : K) N), w' ∉ Zc →
          (B₁ : ↥(Omega.upperHalfPlane K₀ K) → K) ⟨(w' : K), hD w'.2⟩ * a w' = 0 := by
        intro w' hw'
        have h1 := hall w'
        rw [hA, hB₁] at h1
        simp only [ZeroMemClass.coe_zero, Pi.zero_apply, zero_mul, Subring.coe_mul, Subring.coe_pow, Pi.mul_apply,
          Pi.pow_apply, Omega.coordSub_apply] at h1
        rw [mul_assoc] at h1
        exact (mul_eq_zero.1 h1).resolve_left (pow_ne_zero _ (sub_ne_zero.2 hw'))
      have hat : (B₁ : ↥(Omega.upperHalfPlane K₀ K) → K) ⟨(z : K), hD hzD⟩ * a ⟨(z : K), hzD⟩ = 0 :=
        eq_of_eqOn_compl_finite ϖ hrk (z : K) N
          (f := fun w' : ↥(disc ϖ (z : K) N) => (B₁ : ↥(Omega.upperHalfPlane K₀ K) → K) ⟨(w' : K), hD w'.2⟩ * a w')
          (g := fun _ => (0 : K)) ((hcontR B₁).mul hca) continuous_const Zc hZc hoff ⟨(z : K), hzD⟩
      rw [hzz] at hat
      show (0 : ↥(Omega.upperHalfPlane K₀ K) → K) z * b _ = (1 : ↥(Omega.upperHalfPlane K₀ K) → K) z * a _
      rw [Pi.zero_apply, Pi.one_apply, zero_mul, one_mul]
      exact ((mul_eq_zero.1 hat).resolve_left hB₁z).symm
  · obtain ⟨A₁, hA₁, hA₁z⟩ :=
      CerednikDrinfeld.Omega.exists_eq_coordSub_pow_ordAt_mul_and_apply_ne_zero K₀ K hrk ϖ hex hfin A hA z
    set m := Omega.ordAt ϖ A z with hm

    have key : ∀ w : ↥(disc ϖ (z : K) N),
        ((w : K) - (z : K)) ^ n * ((B₁ : ↥(Omega.upperHalfPlane K₀ K) → K) ⟨(w : K), hD w.2⟩ * a w) =
          ((w : K) - (z : K)) ^ m * ((A₁ : ↥(Omega.upperHalfPlane K₀ K) → K) ⟨(w : K), hD w.2⟩ * b w) := by
      intro w
      have h1 := hall w
      rw [hB₁, hA₁] at h1
      simp only [Subring.coe_mul, Subring.coe_pow, Pi.mul_apply, Pi.pow_apply, Omega.coordSub_apply] at h1
      rw [mul_assoc, mul_assoc] at h1
      exact h1
    have hnm : n ≤ m := by
      by_contra hlt
      rw [not_le] at hlt
      obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_lt hlt

      have hoff : ∀ w' : ↥(disc ϖ (z : K) N), w' ∉ Zc →
          ((w' : K) - (z : K)) ^ (d + 1) * ((B₁ : ↥(Omega.upperHalfPlane K₀ K) → K) ⟨(w' : K), hD w'.2⟩ * a w') =
          (A₁ : ↥(Omega.upperHalfPlane K₀ K) → K) ⟨(w' : K), hD w'.2⟩ * b w' := by
        intro w' hw'
        have h1 := key w'
        rw [hd, show m + d + 1 = m + (d + 1) by omega, pow_add, mul_assoc] at h1
        exact mul_left_cancel₀ (pow_ne_zero _ (sub_ne_zero.2 hw')) h1
      have hcpow : Continuous (fun w' : ↥(disc ϖ (z : K) N) => ((w' : K) - (z : K)) ^ (d + 1)) :=
        (continuous_subtype_val.sub continuous_const).pow _
      have hat : (((⟨(z : K), hzD⟩ : ↥(disc ϖ (z : K) N)) : K) - (z : K)) ^ (d + 1) *
            ((B₁ : ↥(Omega.upperHalfPlane K₀ K) → K) ⟨(z : K), hD hzD⟩ * a ⟨(z : K), hzD⟩) =
          (A₁ : ↥(Omega.upperHalfPlane K₀ K) → K) ⟨(z : K), hD hzD⟩ * b ⟨(z : K), hzD⟩ :=
        eq_of_eqOn_compl_finite ϖ hrk (z : K) N
          (f := fun w' : ↥(disc ϖ (z : K) N) =>
            ((w' : K) - (z : K)) ^ (d + 1) * ((B₁ : ↥(Omega.upperHalfPlane K₀ K) → K) ⟨(w' : K), hD w'.2⟩ * a w'))
          (g := fun w' : ↥(disc ϖ (z : K) N) => (A₁ : ↥(Omega.upperHalfPlane K₀ K) → K) ⟨(w' : K), hD w'.2⟩ * b w')
          (hcpow.mul ((hcontR B₁).mul hca)) ((hcontR A₁).mul hcb) Zc hZc hoff ⟨(z : K), hzD⟩
      rw [hzz] at hat
      have h0 : (((⟨(z : K), hzD⟩ : ↥(disc ϖ (z : K) N)) : K) - (z : K)) ^ (d + 1) = 0 := by
        rw [show (((⟨(z : K), hzD⟩ : ↥(disc ϖ (z : K) N)) : K)) = (z : K) from rfl, sub_self, zero_pow (Nat.succ_ne_zero d)]
      rw [h0, zero_mul] at hat
      exact (mul_ne_zero hA₁z (hbz ⟨(z : K), hzD⟩ rfl)) hat.symm
    obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hnm
    refine ⟨Omega.coordSub ϖ z ^ d * A₁, B₁, hB₁z, ?_, fun w hw => ?_⟩
    · rw [hA₁, hB₁, hd, pow_add]; ring
    · obtain rfl : w = ⟨(z : K), hzD⟩ := Subtype.ext hw

      have hoff : ∀ w' : ↥(disc ϖ (z : K) N), w' ∉ Zc →
          (B₁ : ↥(Omega.upperHalfPlane K₀ K) → K) ⟨(w' : K), hD w'.2⟩ * a w' =
          ((w' : K) - (z : K)) ^ d * ((A₁ : ↥(Omega.upperHalfPlane K₀ K) → K) ⟨(w' : K), hD w'.2⟩ * b w') := by
        intro w' hw'
        have h1 := key w'
        rw [hd, pow_add, mul_assoc] at h1
        exact mul_left_cancel₀ (pow_ne_zero _ (sub_ne_zero.2 hw')) h1
      have hcpow : Continuous (fun w' : ↥(disc ϖ (z : K) N) => ((w' : K) - (z : K)) ^ d) :=
        (continuous_subtype_val.sub continuous_const).pow _
      have hat : (B₁ : ↥(Omega.upperHalfPlane K₀ K) → K) ⟨(z : K), hD hzD⟩ * a ⟨(z : K), hzD⟩ =
          (((⟨(z : K), hzD⟩ : ↥(disc ϖ (z : K) N)) : K) - (z : K)) ^ d *
            ((A₁ : ↥(Omega.upperHalfPlane K₀ K) → K) ⟨(z : K), hD hzD⟩ * b ⟨(z : K), hzD⟩) :=
        eq_of_eqOn_compl_finite ϖ hrk (z : K) N
          (f := fun w' : ↥(disc ϖ (z : K) N) => (B₁ : ↥(Omega.upperHalfPlane K₀ K) → K) ⟨(w' : K), hD w'.2⟩ * a w')
          (g := fun w' : ↥(disc ϖ (z : K) N) =>
            ((w' : K) - (z : K)) ^ d * ((A₁ : ↥(Omega.upperHalfPlane K₀ K) → K) ⟨(w' : K), hD w'.2⟩ * b w'))
          ((hcontR B₁).mul hca) (hcpow.mul ((hcontR A₁).mul hcb)) Zc hZc hoff ⟨(z : K), hzD⟩
      rw [hzz] at hat
      show ((Omega.coordSub ϖ z ^ d * A₁ : ↥(Omega.holRing ϖ)) : ↥(Omega.upperHalfPlane K₀ K) → K) z * b _ = _
      simp only [Subring.coe_mul, Subring.coe_pow, Pi.mul_apply, Pi.pow_apply, Omega.coordSub_apply]
      rw [hat, mul_assoc]

end

end S_CerednikDrinfeld_Omega_exists_holRing_mul_eq_mul_and_apply_eq_of_holOn_disc
end P2MW
export P2MW.S_CerednikDrinfeld_Omega_exists_holRing_mul_eq_mul_and_apply_eq_of_holOn_disc (solution)
