-- Prove2me | solution 1 for CerednikDrinfeld.Omega.exists_holRing_forall_finite_eq_of_forall_exists_mem_holOn_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/ba3b1df7-ffda-5697-8fe7-d624d46715bb

import Definitions.Def_CerednikDrinfeld_DrinfeldHolomorphic
import Theorems.Thm_CerednikDrinfeld_Omega_finite_setOf_apply_eq_zero_disc_of_mem_holOn
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_Omega_exists_holRing_forall_finite_eq_of_forall_exists_mem_holOn_eq

set_option autoImplicit false

p2m_open "CerednikDrinfeld.Omega P2MW.S_CerednikDrinfeld_Omega_exists_holRing_forall_finite_eq_of_forall_exists_mem_holOn_eq.CerednikDrinfeld.Omega"

namespace CerednikDrinfeld
p2m_export "CerednikDrinfeld" "Omega.finite_setOf_apply_eq_zero_disc_of_mem_holOn"
namespace Omega
p2m_export "CerednikDrinfeld.Omega" "PseudoUniformizer affinoid affinoid_subset_upperHalfPlane affinoid_mono IsExhausted IsHolOn holOn restrictAffinoid holRing upperHalfPlane finite_setOf_apply_eq_zero_disc_of_mem_holOn"
namespace GlueAux
p2m_open "CerednikDrinfeld.Omega CerednikDrinfeld"

variable {K₀ : Type} [Field K₀] {K : Type} [Field K] [Algebra K₀ K]
  {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]

theorem isHolOn_restrict {S S' : Set K} (hS : S' ⊆ S) {f : ↥S → K} (hf : IsHolOn K S f) :
    IsHolOn K S' (fun w : ↥S' => f ⟨(w : K), hS w.2⟩) := by
  obtain ⟨r, hr, ⟨b, hb⟩, hlim⟩ := hf
  refine ⟨r, fun k z hz => hr k z (hS hz), ⟨b, fun k w => hb k ⟨(w : K), hS w.2⟩⟩, ?_⟩
  exact hlim.comp (fun w : ↥S' => (⟨(w : K), hS w.2⟩ : ↥S))

theorem mem_affinoid_of_v_sub_le (ϖ : PseudoUniformizer K₀ K) (n : ℕ) {z : K} (hz : z ∈ affinoid ϖ n)
    {w : K} (hw : Valued.v (w - z) ≤ Valued.v (algebraMap K₀ K ϖ.ϖ) ^ (n + 1)) : w ∈ affinoid ϖ n := by
  obtain ⟨hz1, hz2⟩ := hz
  have hp0 := ϖ.pos
  have hp1 := ϖ.lt_one
  have hlt : Valued.v (algebraMap K₀ K ϖ.ϖ) ^ (n + 1) < Valued.v (algebraMap K₀ K ϖ.ϖ) ^ n :=
    pow_lt_pow_right_of_lt_one₀ hp0 hp1 (Nat.lt_succ_self n)
  have hle1 : Valued.v (algebraMap K₀ K ϖ.ϖ) ^ (n + 1) ≤ 1 := pow_le_one₀ zero_le' hp1.le
  have hge1 : (1 : Γ₀) ≤ (Valued.v (algebraMap K₀ K ϖ.ϖ))⁻¹ ^ n := one_le_pow₀ ((one_le_inv₀ hp0).2 hp1.le)
  refine ⟨?_, fun a ha => ?_⟩
  · have : w = (w - z) + z := by ring
    rw [this]
    refine (Valuation.map_add _ _ _).trans (max_le (hw.trans (hle1.trans hge1)) hz1)
  · have hza := hz2 a ha
    have hlt' : Valued.v (w - z) < Valued.v (z - algebraMap K₀ K a) := lt_of_le_of_lt hw (lt_of_lt_of_le hlt hza)
    have : w - algebraMap K₀ K a = (z - algebraMap K₀ K a) + (w - z) := by ring
    rw [this, Valuation.map_add_eq_of_lt_left _ hlt']
    exact hza

end CerednikDrinfeld.Omega.GlueAux

open CerednikDrinfeld.Omega.GlueAux in
theorem solution
    (K₀ : Type) [Field K₀] (K : Type) [Field K] [Algebra K₀ K]
    {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀] [CompleteSpace K] [IsAlgClosed K]
    (ϖ : PseudoUniformizer K₀ K)
    (hrk : ∀ x y : K, Valued.v x < 1 → y ≠ 0 → ∃ n : ℕ, Valued.v x ^ n ≤ Valued.v y)
    (hex : IsExhausted ϖ)
    (Ψ : ↥(upperHalfPlane K₀ K) → K)
    (h : ∀ n : ℕ, ∃ ψ : ↥(affinoid ϖ n) → K, ψ ∈ holOn K (affinoid ϖ n) ∧
      ∃ Z : Set ↥(affinoid ϖ n), Z.Finite ∧
        ∀ z : ↥(affinoid ϖ n), z ∉ Z → Ψ ⟨(z : K), affinoid_subset_upperHalfPlane ϖ n z.2⟩ = ψ z) :
    ∃ Φ : ↥(holRing ϖ), ∀ n : ℕ, ∃ Z : Set ↥(affinoid ϖ n), Z.Finite ∧
      ∀ z : ↥(affinoid ϖ n), z ∉ Z →
        Ψ ⟨(z : K), affinoid_subset_upperHalfPlane ϖ n z.2⟩ =
          (Φ : ↥(upperHalfPlane K₀ K) → K) ⟨(z : K), affinoid_subset_upperHalfPlane ϖ n z.2⟩ := by
  classical
  choose ψ hψ Z hZfin hZ using h
  have hp0 := ϖ.pos
  have hp1 := ϖ.lt_one
  have hπne : ∀ n : ℕ, (algebraMap K₀ K ϖ.ϖ) ^ (n + 1) ≠ 0 := fun n => by
    intro h0
    have := congrArg Valued.v h0
    rw [map_pow, map_zero] at this
    exact pow_ne_zero _ hp0.ne' this

  have agree : ∀ (n m : ℕ) (hnm : n ≤ m) (z : ↥(affinoid ϖ n)),
      ψ n z = ψ m ⟨(z : K), affinoid_mono ϖ hnm z.2⟩ := by
    intro n m hnm z
    have hincl : IsHolOn K (affinoid ϖ n) (fun w : ↥(affinoid ϖ n) => ψ m ⟨(w : K), affinoid_mono ϖ hnm w.2⟩) :=
      isHolOn_restrict (affinoid_mono ϖ hnm) (hψ m)
    have hg : (ψ n - fun w : ↥(affinoid ϖ n) => ψ m ⟨(w : K), affinoid_mono ϖ hnm w.2⟩) ∈ holOn K (affinoid ϖ n) :=
      sub_mem (hψ n) hincl
    have hg0 : ∀ w : ↥(affinoid ϖ n), w ∉ Z n →
        (⟨(w : K), affinoid_mono ϖ hnm w.2⟩ : ↥(affinoid ϖ m)) ∉ Z m →
        (ψ n - fun w : ↥(affinoid ϖ n) => ψ m ⟨(w : K), affinoid_mono ϖ hnm w.2⟩) w = 0 := by
      intro w h1 h2
      rw [Pi.sub_apply, ← hZ n w h1, ← hZ m _ h2, sub_self]

    have hdisc := CerednikDrinfeld.Omega.finite_setOf_apply_eq_zero_disc_of_mem_holOn K hrk (affinoid ϖ n) (z : K)
      ((algebraMap K₀ K ϖ.ϖ) ^ (n + 1)) (hπne n) ∅ (by simp)
      (fun w hw _ => mem_affinoid_of_v_sub_le ϖ n z.2 (by rwa [map_pow] at hw)) hg
    rcases hdisc with hall | hfin
    · have := hall z (by rw [sub_self, map_zero]; exact zero_le') (by simp)
      rwa [Pi.sub_apply, sub_eq_zero] at this
    · exfalso

      set pt : ℕ → ↥(affinoid ϖ n) := fun k => ⟨(z : K) + (algebraMap K₀ K ϖ.ϖ) ^ (n + 1 + k),
        mem_affinoid_of_v_sub_le ϖ n z.2 (by
          rw [add_sub_cancel_left, map_pow, pow_add]
          exact mul_le_of_le_one_right' (pow_le_one₀ zero_le' hp1.le))⟩ with hpt
      have hinj : Function.Injective pt := by
        intro k l hkl
        have h1 : (algebraMap K₀ K ϖ.ϖ) ^ (n + 1 + k) = (algebraMap K₀ K ϖ.ϖ) ^ (n + 1 + l) := by
          have := congrArg (fun x : ↥(affinoid ϖ n) => (x : K)) hkl
          simpa [hpt] using this
        have h2 := congrArg Valued.v h1
        rw [map_pow, map_pow] at h2
        have := (pow_right_strictAnti₀ hp0 hp1).injective h2
        omega
      have hsub : Set.range pt \ (Z n ∪ (fun w : ↥(affinoid ϖ n) =>
          (⟨(w : K), affinoid_mono ϖ hnm w.2⟩ : ↥(affinoid ϖ m))) ⁻¹' Z m) ⊆
          {w : ↥(affinoid ϖ n) | Valued.v ((w : K) - (z : K)) ≤ Valued.v ((algebraMap K₀ K ϖ.ϖ) ^ (n + 1)) ∧
            (∀ ζ ∈ (∅ : Finset K), Valued.v ((algebraMap K₀ K ϖ.ϖ) ^ (n + 1)) ≤ Valued.v ((w : K) - ζ)) ∧
            (ψ n - fun w : ↥(affinoid ϖ n) => ψ m ⟨(w : K), affinoid_mono ϖ hnm w.2⟩) w = 0} := by
        rintro w ⟨⟨k, rfl⟩, hw⟩
        rw [Set.mem_union, not_or, Set.mem_preimage] at hw
        refine ⟨?_, by simp, hg0 _ hw.1 hw.2⟩
        show Valued.v ((z : K) + (algebraMap K₀ K ϖ.ϖ) ^ (n + 1 + k) - (z : K)) ≤ _
        rw [add_sub_cancel_left, map_pow, map_pow, pow_add]
        exact mul_le_of_le_one_right' (pow_le_one₀ zero_le' hp1.le)
      have hinf : (Set.range pt \ (Z n ∪ (fun w : ↥(affinoid ϖ n) =>
          (⟨(w : K), affinoid_mono ϖ hnm w.2⟩ : ↥(affinoid ϖ m))) ⁻¹' Z m)).Infinite :=
        (Set.infinite_range_of_injective hinj).diff
          ((hZfin n).union ((hZfin m).preimage fun _ _ _ _ hxy => Subtype.ext (by
            have := congrArg (fun x : ↥(affinoid ϖ m) => (x : K)) hxy; exact this)))
      exact hinf (hfin.subset hsub)

  have hexz : ∀ z : ↥(upperHalfPlane K₀ K), ∃ n : ℕ, (z : K) ∈ affinoid ϖ n := fun z => hex (z : K) z.2
  choose nz hnz using hexz
  let Φf : ↥(upperHalfPlane K₀ K) → K := fun z => ψ (nz z) ⟨(z : K), hnz z⟩
  have hres : ∀ (n : ℕ) (w : ↥(affinoid ϖ n)),
      Φf ⟨(w : K), affinoid_subset_upperHalfPlane ϖ n w.2⟩ = ψ n w := by
    intro n w
    show ψ (nz ⟨(w : K), _⟩) ⟨(w : K), _⟩ = ψ n w
    set N := nz ⟨(w : K), affinoid_subset_upperHalfPlane ϖ n w.2⟩ with hN
    rw [agree N (max n N) (le_max_right _ _) ⟨(w : K), hnz _⟩, agree n (max n N) (le_max_left _ _) w]
  have hΦ : Φf ∈ holRing ϖ := by
    intro n
    have : restrictAffinoid ϖ n Φf = ψ n := funext fun w => hres n w
    rw [this]
    exact hψ n
  refine ⟨⟨Φf, hΦ⟩, fun n => ⟨Z n, hZfin n, fun z hz => ?_⟩⟩
  rw [hZ n z hz]
  exact (hres n z).symm

end S_CerednikDrinfeld_Omega_exists_holRing_forall_finite_eq_of_forall_exists_mem_holOn_eq
end P2MW
export P2MW.S_CerednikDrinfeld_Omega_exists_holRing_forall_finite_eq_of_forall_exists_mem_holOn_eq (solution)
