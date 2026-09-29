-- Prove2me | solution 1 for CerednikDrinfeld.FormalOmega.MumfordTower.exists_action_forall_q_eq_q_comp
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/6eca4771-2108-5266-91d7-78941bee2e09

import Mathlib
import Definitions.Def_CerednikDrinfeld_MumfordTower
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_FormalOmega_MumfordTower_exists_action_forall_q_eq_q_comp

set_option autoImplicit false

open scoped TensorProduct MatrixGroups
open CategoryTheory AlgebraicGeometry LT.LatticeTree CerednikDrinfeld CerednikDrinfeld.FormalOmega

namespace F2d13

variable {𝒪 : Type} [CommRing 𝒪] {π : 𝒪} {K₀ : Type} [Field K₀] [Algebra 𝒪 K₀] {r : ℕ}
  {g₁ : Matrix.GeneralLinearGroup (Fin 2) K₀} {N : Subgroup (PGL(2, K₀))}

theorem isPullback_inv_iff (B : Type) [CommRing B] [Algebra 𝒪 B] (g : Matrix.GeneralLinearGroup (Fin 2) K₀)
    (d d' : (Omega K₀ π).obj B) :
    DeligneDatum.IsPullback (K := K₀) (π := π) B g⁻¹ d d' ↔ d' = (Omega.action K₀ π).act B g d := by
  constructor
  · intro h; exact DeligneDatum.ext' (funext fun M => h M)
  · intro h M; rw [h]; rfl

theorem pow_succ_eq_zero {B : Type} [CommRing B] [Algebra 𝒪 B] {n : ℕ} (hB : (algebraMap 𝒪 B π) ^ (n + 1) = 0) :
    (algebraMap 𝒪 B π) ^ (n + 1 + 1) = 0 := by rw [pow_succ, hB, zero_mul]

theorem norm_inv (g : Matrix.GeneralLinearGroup (Fin 2) K₀)
    (hg : ∀ x : PGL(2, K₀), x ∈ N ↔ Matrix.ProjGenLinGroup.mk g * x * (Matrix.ProjGenLinGroup.mk g)⁻¹ ∈ N) :
    ∀ x : PGL(2, K₀), x ∈ N ↔ Matrix.ProjGenLinGroup.mk g⁻¹ * x * (Matrix.ProjGenLinGroup.mk g⁻¹)⁻¹ ∈ N := by
  intro x
  have h := hg (Matrix.ProjGenLinGroup.mk g⁻¹ * x * (Matrix.ProjGenLinGroup.mk g⁻¹)⁻¹)
  have e : Matrix.ProjGenLinGroup.mk g * (Matrix.ProjGenLinGroup.mk g⁻¹ * x * (Matrix.ProjGenLinGroup.mk g⁻¹)⁻¹) *
      (Matrix.ProjGenLinGroup.mk g)⁻¹ = x := by
    rw [map_inv]; group
  rw [e] at h
  exact h.symm

variable (D : MumfordTower 𝒪 π K₀ r g₁ N)

theorem hom_ext (n : ℕ) {T : Scheme.{0}} (b b' : D.Z n ⟶ T)
    (h : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (hB : (algebraMap 𝒪 B π) ^ (n + 1) = 0) (P : (Omega K₀ π).obj B),
      D.q n B hB P ≫ b = D.q n B hB P ≫ b') : b = b' := by
  have hu := D.univ_lvl n T (fun B _ _ hB P => D.q n B hB P ≫ b')
    (fun B _ _ B' _ _ hB hB' φ P => by
      show D.q n B' hB' ((Omega K₀ π).map φ P) ≫ b' = Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ D.q n B hB P ≫ b'
      rw [D.q_natural n B B' hB hB' φ P, Category.assoc])
    (fun B _ _ hB g hg P P' hPP' => by
      show D.q n B hB P' ≫ b' = D.q n B hB P ≫ b'
      rw [D.q_inv n B hB g hg P P' hPP'])
  exact hu.unique h (fun B _ _ hB P => rfl)

theorem natural_act (n : ℕ) (g : Matrix.GeneralLinearGroup (Fin 2) K₀) :
    ∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (B' : Type) [CommRing B'] [Algebra 𝒪 B']
      (hB : (algebraMap 𝒪 B π) ^ (n + 1) = 0) (hB' : (algebraMap 𝒪 B' π) ^ (n + 1) = 0) (φ : B →ₐ[𝒪] B') (P : (Omega K₀ π).obj B),
      D.q n B' hB' ((Omega.action K₀ π).act B' g ((Omega K₀ π).map φ P)) =
        Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ D.q n B hB ((Omega.action K₀ π).act B g P) := by
  intro B _ _ B' _ _ hB hB' φ P
  rw [← (Omega.action K₀ π).act_map φ g P, D.q_natural n B B' hB hB' φ]

theorem invariant_act (n : ℕ) (g : Matrix.GeneralLinearGroup (Fin 2) K₀)
    (hg : ∀ x : PGL(2, K₀), x ∈ N ↔ Matrix.ProjGenLinGroup.mk g * x * (Matrix.ProjGenLinGroup.mk g)⁻¹ ∈ N) :
    ∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (hB : (algebraMap 𝒪 B π) ^ (n + 1) = 0)
      (h : Matrix.GeneralLinearGroup (Fin 2) K₀), Matrix.ProjGenLinGroup.mk h ∈ N →
      ∀ P P' : (Omega K₀ π).obj B, DeligneDatum.IsPullback (K := K₀) (π := π) B h⁻¹ P P' →
        D.q n B hB ((Omega.action K₀ π).act B g P') = D.q n B hB ((Omega.action K₀ π).act B g P) := by
  intro B _ _ hB h hh P P' hPP'
  rw [isPullback_inv_iff] at hPP'
  rw [hPP']
  have e : (Omega.action K₀ π).act B g ((Omega.action K₀ π).act B h P) =
      (Omega.action K₀ π).act B (g * h * g⁻¹) ((Omega.action K₀ π).act B g P) := by
    rw [← (Omega.action K₀ π).act_mul, ← (Omega.action K₀ π).act_mul, inv_mul_cancel_right]
  rw [e]
  have hmem : Matrix.ProjGenLinGroup.mk (g * h * g⁻¹) ∈ N := by
    rw [map_mul, map_mul, map_inv]; exact (hg _).1 hh
  exact D.q_inv n B hB (g * h * g⁻¹) hmem _ _ ((isPullback_inv_iff B _ _ _).2 rfl)

theorem exu (n : ℕ) (g : Matrix.GeneralLinearGroup (Fin 2) K₀)
    (hg : ∀ x : PGL(2, K₀), x ∈ N ↔ Matrix.ProjGenLinGroup.mk g * x * (Matrix.ProjGenLinGroup.mk g)⁻¹ ∈ N) :
    ∃! u : D.Z n ⟶ D.Z n, ∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (hB : (algebraMap 𝒪 B π) ^ (n + 1) = 0)
      (P : (Omega K₀ π).obj B), D.q n B hB P ≫ u = D.q n B hB ((Omega.action K₀ π).act B g P) :=
  D.univ_lvl n (D.Z n) (fun B _ _ hB P => D.q n B hB ((Omega.action K₀ π).act B g P)) (natural_act D n g)
    (fun B _ _ hB h hh P P' hPP' => invariant_act D n g hg B hB h hh P P' hPP')

noncomputable def U (n : ℕ) (g : Matrix.GeneralLinearGroup (Fin 2) K₀)
    (hg : ∀ x : PGL(2, K₀), x ∈ N ↔ Matrix.ProjGenLinGroup.mk g * x * (Matrix.ProjGenLinGroup.mk g)⁻¹ ∈ N) :
    D.Z n ⟶ D.Z n :=
  (exu D n g hg).exists.choose

theorem U_spec (n : ℕ) (g : Matrix.GeneralLinearGroup (Fin 2) K₀)
    (hg : ∀ x : PGL(2, K₀), x ∈ N ↔ Matrix.ProjGenLinGroup.mk g * x * (Matrix.ProjGenLinGroup.mk g)⁻¹ ∈ N)
    (B : Type) [CommRing B] [Algebra 𝒪 B] (hB : (algebraMap 𝒪 B π) ^ (n + 1) = 0) (P : (Omega K₀ π).obj B) :
    D.q n B hB P ≫ U D n g hg = D.q n B hB ((Omega.action K₀ π).act B g P) :=
  (exu D n g hg).exists.choose_spec B hB P

theorem q_act_zb (n : ℕ) (g : Matrix.GeneralLinearGroup (Fin 2) K₀)
    (B : Type) [CommRing B] [Algebra 𝒪 B] (hB : (algebraMap 𝒪 B π) ^ (n + 1) = 0) (P : (Omega K₀ π).obj B) :
    D.q n B hB ((Omega.action K₀ π).act B g P) ≫ D.zb n = D.q n B hB P ≫ D.zb n := by
  haveI : IsClosedImmersion (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 (𝒪 ⧸ Ideal.span {π ^ (n + 1)})))) :=
    IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  rw [← cancel_mono (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 (𝒪 ⧸ Ideal.span {π ^ (n + 1)})))), Category.assoc,
    Category.assoc, D.q_over, D.q_over]

end F2d13

open F2d13 in
theorem solution
    (𝒪 : Type) [CommRing 𝒪] (π : 𝒪) (K₀ : Type) [Field K₀] [Algebra 𝒪 K₀] (r : ℕ)
    (g₁ : Matrix.GeneralLinearGroup (Fin 2) K₀) (N : Subgroup (PGL(2, K₀)))
    (D : MumfordTower 𝒪 π K₀ r g₁ N) :
    ∃ a : ∀ (g : Matrix.GeneralLinearGroup (Fin 2) K₀),
        (∀ x : PGL(2, K₀), x ∈ N ↔ Matrix.ProjGenLinGroup.mk g * x * (Matrix.ProjGenLinGroup.mk g)⁻¹ ∈ N) → ∀ n : ℕ, D.Z n ≅ D.Z n,

      (∀ g hg (n : ℕ), (a g hg n).hom ≫ D.zb n = D.zb n) ∧

      (∀ g hg (n : ℕ), D.zt n ≫ (a g hg (n + 1)).hom = (a g hg n).hom ≫ D.zt n) ∧

      (∀ g hg (n : ℕ) (B : Type) [CommRing B] [Algebra 𝒪 B] (hB : (algebraMap 𝒪 B π) ^ (n + 1) = 0)
        (P P' : (Omega K₀ π).obj B), DeligneDatum.IsPullback (K := K₀) (π := π) B g⁻¹ P P' →
        D.q n B hB P' = D.q n B hB P ≫ (a g hg n).hom) ∧

      (∀ g hg (n : ℕ) (b : D.Z n ⟶ D.Z n),
        (∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (hB : (algebraMap 𝒪 B π) ^ (n + 1) = 0)
          (P P' : (Omega K₀ π).obj B), DeligneDatum.IsPullback (K := K₀) (π := π) B g⁻¹ P P' →
          D.q n B hB P' = D.q n B hB P ≫ b) → b = (a g hg n).hom) ∧

      (∀ g hg (n : ℕ), Matrix.ProjGenLinGroup.mk g ∈ N → (a g hg n).hom = 𝟙 (D.Z n)) ∧

      (∀ g hg g' hg' (hgg' : ∀ x : PGL(2, K₀), x ∈ N ↔
          Matrix.ProjGenLinGroup.mk (g * g') * x * (Matrix.ProjGenLinGroup.mk (g * g'))⁻¹ ∈ N) (n : ℕ),
        (a (g * g') hgg' n).hom = (a g' hg' n).hom ≫ (a g hg n).hom) := by
  classical
  refine ⟨fun g hg n => ⟨U D n g hg, U D n g⁻¹ (norm_inv g hg), ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
  ·
    apply hom_ext D n
    intro B _ _ hB P
    rw [← Category.assoc, U_spec, U_spec, ← (Omega.action K₀ π).act_mul, inv_mul_cancel, (Omega.action K₀ π).act_one,
      Category.comp_id]
  ·
    apply hom_ext D n
    intro B _ _ hB P
    rw [← Category.assoc, U_spec, U_spec, ← (Omega.action K₀ π).act_mul, mul_inv_cancel, (Omega.action K₀ π).act_one,
      Category.comp_id]
  ·
    intro g hg n
    apply hom_ext D n
    intro B _ _ hB P
    show D.q n B hB P ≫ U D n g hg ≫ D.zb n = D.q n B hB P ≫ D.zb n
    rw [← Category.assoc, U_spec, q_act_zb]
  ·
    intro g hg n
    apply hom_ext D n
    intro B _ _ hB P
    show D.q n B hB P ≫ D.zt n ≫ U D (n + 1) g hg = D.q n B hB P ≫ U D n g hg ≫ D.zt n
    rw [← Category.assoc, ← D.q_zt n B hB (pow_succ_eq_zero hB) P, U_spec, D.q_zt n B hB (pow_succ_eq_zero hB),
      ← Category.assoc, U_spec]
  ·
    intro g hg n B _ _ hB P P' hPP'
    rw [isPullback_inv_iff] at hPP'
    show D.q n B hB P' = D.q n B hB P ≫ U D n g hg
    rw [hPP', U_spec]
  ·
    intro g hg n b hb
    show b = U D n g hg
    apply (exu D n g hg).unique
    · intro B _ _ hB P
      exact (hb B hB P _ ((isPullback_inv_iff B g P _).2 rfl)).symm
    · intro B _ _ hB P
      exact U_spec D n g hg B hB P
  ·
    intro g hg n hgN
    apply hom_ext D n
    intro B _ _ hB P
    show D.q n B hB P ≫ U D n g hg = D.q n B hB P ≫ 𝟙 _
    rw [U_spec, Category.comp_id]
    exact D.q_inv n B hB g hgN P _ ((isPullback_inv_iff B g P _).2 rfl)
  ·
    intro g hg g' hg' hgg' n
    apply hom_ext D n
    intro B _ _ hB P
    show D.q n B hB P ≫ U D n (g * g') hgg' = D.q n B hB P ≫ U D n g' hg' ≫ U D n g hg
    rw [U_spec, ← Category.assoc, U_spec, U_spec, (Omega.action K₀ π).act_mul]

end S_CerednikDrinfeld_FormalOmega_MumfordTower_exists_action_forall_q_eq_q_comp
end P2MW
export P2MW.S_CerednikDrinfeld_FormalOmega_MumfordTower_exists_action_forall_q_eq_q_comp (solution)
