-- Prove2me | solution 1 for Deformation.DieudonneModule.exists_mvPowerSeries_coeff_eq_apply_of_forall_map_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/f4ce82a7-3e72-5c8f-a5fb-15d54343fb9e

import Mathlib
import Definitions.Def_Dieudonne_DatumAndHonda
import Definitions.Def_Dieudonne_WittVectorHom
import Definitions.Def_Dieudonne_WittHomColimit
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Deformation_DieudonneModule_exists_mvPowerSeries_coeff_eq_apply_of_forall_map_eq

universe v

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 80000
set_option Elab.async false

open Function

namespace Deformation
p2m_export "Deformation" "TruncWitt.map TruncWitt.coeff_map wittHom counit_coeff_of_mem_wittHom coe_wittHomMap TruncWitt.shiftLE TruncWitt.coeff_shiftLE wittHomShiftLE coe_wittHomShiftLE DieudonneModule DieudonneModule.of DieudonneModule.of_shiftLE DieudonneModule.exists_of DieudonneModule.of_eq_of_iff DieudonneModule.map DieudonneModule.map_of"
p2m_open "Deformation"

namespace CovectorComponents

section EndCoeff

variable {p : ℕ} {n m : ℕ} {R : Type*} {S : Type*} [CommRing R] [CommRing S]

def endCoeff (k : ℕ) (x : TruncatedWittVector p n R) : R :=
  if hk : k < n then x.coeff ⟨n - 1 - k, by omega⟩ else 0

theorem endCoeff_of_lt (k : ℕ) (x : TruncatedWittVector p n R) (hk : k < n) :
    endCoeff k x = x.coeff ⟨n - 1 - k, by omega⟩ := dif_pos hk

theorem endCoeff_of_le (k : ℕ) (x : TruncatedWittVector p n R) (hk : n ≤ k) :
    endCoeff k x = 0 := dif_neg (by omega)

variable [hp : Fact p.Prime]

theorem endCoeff_shiftLE (h : n ≤ m) (k : ℕ) (x : TruncatedWittVector p n R) :
    endCoeff k (TruncWitt.shiftLE h x) = endCoeff k x := by
  unfold endCoeff
  by_cases hk : k < n
  · have hkm : k < m := by omega
    rw [dif_pos hkm, dif_pos hk, TruncWitt.coeff_shiftLE,
      dif_pos (show m - n ≤ m - 1 - k by omega)]
    congr 1
    exact Fin.ext (by simp only []; omega)
  · rw [dif_neg hk]
    by_cases hkm : k < m
    · rw [dif_pos hkm, TruncWitt.coeff_shiftLE, dif_neg (show ¬ (m - n ≤ m - 1 - k) by omega)]
    · rw [dif_neg hkm]

theorem endCoeff_map (f : R →+* S) (k : ℕ) (x : TruncatedWittVector p n R) :
    endCoeff k (TruncWitt.map f x) = f (endCoeff k x) := by
  unfold endCoeff
  split_ifs
  · exact TruncWitt.coeff_map f x _
  · exact (map_zero f).symm

end EndCoeff

section Comp

variable {R : Type*} [CommRing R] {p : ℕ} [hp : Fact p.Prime]
variable {A : Type*} [CommRing A] [Bialgebra R A] {B : Type*} [CommRing B] [Bialgebra R B]

theorem endCoeff_eq_of_of_eq_of {n n' : ℕ} (u : wittHom R p n A) (u' : wittHom R p n' A)
    (h : DieudonneModule.of R p A n u = DieudonneModule.of R p A n' u') (k : ℕ) :
    endCoeff k (u : TruncatedWittVector p n A) = endCoeff k (u' : TruncatedWittVector p n' A) := by
  rw [DieudonneModule.of_eq_of_iff] at h
  have h' := congrArg
    (fun w : wittHom R p (max n n') A => endCoeff k (w : TruncatedWittVector p (max n n') A)) h
  simpa only [coe_wittHomShiftLE, endCoeff_shiftLE] using h'

noncomputable def component (z : DieudonneModule R p A) (k : ℕ) : A :=
  endCoeff k (Subtype.val (DieudonneModule.exists_of z).choose_spec.choose)

theorem component_of {n : ℕ} (u : wittHom R p n A) (k : ℕ) :
    component (DieudonneModule.of R p A n u) k = endCoeff k (u : TruncatedWittVector p n A) := by
  unfold component
  exact endCoeff_eq_of_of_eq_of _ _
    (DieudonneModule.exists_of (DieudonneModule.of R p A n u)).choose_spec.choose_spec k

theorem component_map (φ : A →ₐc[R] B) (z : DieudonneModule R p A) (k : ℕ) :
    component (DieudonneModule.map R p φ z) k = φ (component z k) := by
  obtain ⟨n, u, rfl⟩ := DieudonneModule.exists_of z
  rw [DieudonneModule.map_of, component_of, component_of, coe_wittHomMap, endCoeff_map]
  rfl

theorem counit_component (z : DieudonneModule R p A) (k : ℕ) :
    Coalgebra.counit (R := R) (component z k) = 0 := by
  obtain ⟨n, u, rfl⟩ := DieudonneModule.exists_of z
  rw [component_of]
  unfold endCoeff
  split_ifs with hk
  · exact counit_coeff_of_mem_wittHom u.2 _
  · exact map_zero _

theorem component_of_eq_zero_of_le {n : ℕ} (u : wittHom R p n A) (k : ℕ) (hk : n ≤ k) :
    component (DieudonneModule.of R p A n u) k = 0 := by
  rw [component_of, endCoeff_of_le _ _ hk]

end Comp

theorem algHom_apply_eq_constantCoeff {K : Type*} [Field K] {σ : Type*}
    (φ : MvPowerSeries σ K →ₐ[K] K) (G : MvPowerSeries σ K) :
    φ G = MvPowerSeries.constantCoeff G := by
  have hsurj : Function.Surjective φ := fun c => ⟨algebraMap K _ c, φ.commutes c⟩
  have hker : RingHom.ker φ = IsLocalRing.maximalIdeal (MvPowerSeries σ K) :=
    IsLocalRing.eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective φ hsurj)
  have hmem : G - MvPowerSeries.C (MvPowerSeries.constantCoeff G) ∈ RingHom.ker φ := by
    rw [hker, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
      MvPowerSeries.isUnit_iff_constantCoeff, map_sub, MvPowerSeries.constantCoeff_C, sub_self]
    exact not_isUnit_zero
  rw [RingHom.mem_ker, map_sub, sub_eq_zero] at hmem
  rw [hmem, MvPowerSeries.c_eq_algebraMap, AlgHom.commutes]
  rfl

end CovectorComponents

end Deformation

open _root_.Deformation _root_.P2MW.S_Deformation_DieudonneModule_exists_mvPowerSeries_coeff_eq_apply_of_forall_map_eq.Deformation Deformation.CovectorComponents in

theorem solution
    (p : ℕ) [Fact p.Prime] {d : ℕ}
    (H : ℕ → Type v) [∀ v, CommRing (H v)] [∀ v, Bialgebra (ZMod p) (H v)]
    (s : ∀ v, H (v + 1) →ₐc[ZMod p] H v)
    (π : ∀ v, MvPowerSeries (Fin d) (ZMod p) →ₐ[ZMod p] H v)
    (hπs : ∀ v, (s v : H (v + 1) →ₐ[ZMod p] H v).comp (π (v + 1)) = π v)
    (hπε : ∀ v i, Coalgebra.counit (R := ZMod p) (π v (MvPowerSeries.X i)) = 0)
    (hπinj : ∀ G : MvPowerSeries (Fin d) (ZMod p), (∀ v, π v G = 0) → G = 0)
    (hπsurjj : ∀ z : ∀ v, H v, (∀ v, s v (z (v + 1)) = z v) →
      ∃ G : MvPowerSeries (Fin d) (ZMod p), ∀ v, π v G = z v)
    (hπker : ∀ N : ℕ, ∃ v, RingHom.ker (π v) ≤
      (Ideal.span (Set.range (MvPowerSeries.X : Fin d → MvPowerSeries (Fin d) (ZMod p)))) ^ N)
    (m : ∀ v, Deformation.DieudonneModule (ZMod p) p (H v))
    (hm : ∀ v, Deformation.DieudonneModule.map (ZMod p) p (s v) (m (v + 1)) = m v) :
    ∃ abar : ℕ → MvPowerSeries (Fin d) (ZMod p),
      (∀ k, MvPowerSeries.constantCoeff (abar k) = 0) ∧
      (∀ N : ℕ, ∃ k₀, ∀ k, k₀ ≤ k →
        abar k ∈ (Ideal.span (Set.range (MvPowerSeries.X : Fin d → MvPowerSeries (Fin d) (ZMod p)))) ^ N) ∧
      (∀ (v n : ℕ) (u : Deformation.wittHom (ZMod p) p n (H v)),
        Deformation.DieudonneModule.of (ZMod p) p (H v) n u = m v →
        ∀ (k : ℕ) (hk : k < n),
          (u : TruncatedWittVector p n (H v)).coeff ⟨n - 1 - k, by omega⟩ = π v (abar k)) ∧
      (∀ abar' : ℕ → MvPowerSeries (Fin d) (ZMod p),
        (∀ (v n : ℕ) (u : Deformation.wittHom (ZMod p) p n (H v)),
          Deformation.DieudonneModule.of (ZMod p) p (H v) n u = m v →
          ∀ (k : ℕ) (hk : k < n),
            (u : TruncatedWittVector p n (H v)).coeff ⟨n - 1 - k, by omega⟩ = π v (abar' k)) →
        abar' = abar) := by
  classical

  have hzs : ∀ k v, s v (component (m (v + 1)) k) = component (m v) k := fun k v => by
    rw [← hm v, component_map]
  choose abar habar using fun k => hπsurjj (fun v => component (m v) k) (hzs k)

  have hcoef : ∀ (v n : ℕ) (u : wittHom (ZMod p) p n (H v)),
      DieudonneModule.of (ZMod p) p (H v) n u = m v → ∀ (k : ℕ) (hk : k < n),
        (u : TruncatedWittVector p n (H v)).coeff ⟨n - 1 - k, by omega⟩ = π v (abar k) := by
    intro v n u hu k hk
    rw [habar, ← hu, component_of, endCoeff_of_lt _ _ hk]
  refine ⟨abar, fun k => ?_, fun N => ?_, hcoef, fun abar' h' => ?_⟩
  ·
    rw [← algHom_apply_eq_constantCoeff ((Bialgebra.counitAlgHom (ZMod p) (H 0)).comp (π 0)),
      AlgHom.comp_apply, habar, Bialgebra.counitAlgHom_apply]
    exact counit_component (m 0) k
  ·
    obtain ⟨v₀, hv₀⟩ := hπker N
    obtain ⟨n₀, u₀, hu₀⟩ := DieudonneModule.exists_of (m v₀)
    refine ⟨n₀, fun k hk => hv₀ ?_⟩
    rw [RingHom.mem_ker, habar, ← hu₀, component_of_eq_zero_of_le _ _ hk]
  ·
    funext k
    refine sub_eq_zero.1 (hπinj _ fun v => ?_)
    obtain ⟨n₀, u₀, hu₀⟩ := DieudonneModule.exists_of (m v)
    have hle : n₀ ≤ n₀ + (k + 1) := Nat.le_add_right _ _
    have hu : DieudonneModule.of (ZMod p) p (H v) (n₀ + (k + 1))
        (wittHomShiftLE (ZMod p) p (H v) hle u₀) = m v := by
      rw [DieudonneModule.of_shiftLE, hu₀]
    have hk : k < n₀ + (k + 1) := by omega
    rw [map_sub, ← h' v _ _ hu k hk, ← hcoef v _ _ hu k hk, sub_self]

end S_Deformation_DieudonneModule_exists_mvPowerSeries_coeff_eq_apply_of_forall_map_eq
end P2MW
export P2MW.S_Deformation_DieudonneModule_exists_mvPowerSeries_coeff_eq_apply_of_forall_map_eq (solution)
