-- Prove2me | solution 1 for Formalism.L2.Geo.Def.G1.dual_frame
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T10:01:33.889522+00:00
-- url     : https://prove2.me/submissions/43a3756d-f76e-47cf-b78e-2de207e8e894

import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_DualLattice
import Definitions.Def_Formalism_QuotientMetricDivisors_Statement
import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Formalism_LocalToGlobal_LatticeGeometry_GeometryDefinitions_DualFrame
import Theorems.Thm_Formalism_HermitianLatticesTheory_dualLattice_dualBasis


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Module Matrix
open Formalism Formalism.L2 Formalism.L2.Geo Formalism.L2.Geo.Def Formalism.L2.Geo.Def.G1
variable {R K V : Type*} [CommRing R] [IsDedekindDomain R] [Field K] [StarRing K] [Algebra R K]
  [IsFractionRing R K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module R V]
  [IsScalarTower R K V]
namespace Formalism.L2.Geo.Def.G1
theorem _root_.solution (h : V →ₗ⋆[K] V →ₗ[K] K) (hs : h.IsSymm) (hnd : h.Nondegenerate)
    (hstar : ∀ r : R, star (algebraMap R K r) ∈ Set.range (algebraMap R K))
    (L : Submodule R V) (hL : Submodule.IsLattice K L) :
    ∃ (n : ℕ) (g w : Fin n → V), (∀ i, g i ∈ L) ∧ (∀ i, w i ∈ Formalism.HermitianLatticesTheory.dual h L) ∧
      ∀ z : V, z = ∑ i, h (w i) z • g i := by
  classical
  have hsp : Submodule.span K (L : Set V) = ⊤ := hL.span_eq_top

  obtain ⟨s, hsL, hspan, hli⟩ := exists_linearIndependent K (L : Set V)
  haveI : Fintype s := (LinearIndependent.setFinite hli).fintype
  let b : Module.Basis s K V := Module.Basis.mk hli (by rw [Subtype.range_coe, hspan, hsp])
  have hbL : ∀ j, b j ∈ L := fun j => by
    rw [show b j = (j : V) from Module.Basis.mk_apply hli _ j]; exact hsL j.2
  obtain ⟨bs, hbs⟩ := Formalism.HermitianLatticesTheory.dualLattice_dualBasis h hnd b
  have hbs' : ∀ j k, h (bs j) (b k) = if k = j then 1 else 0 := fun j k => by
    rw [← hs.eq (b k) (bs j), hbs k j]; split_ifs <;> simp
  have hcoord : ∀ z : V, z = ∑ j, h (bs j) z • b j := by
    have hlin : (LinearMap.id : V →ₗ[K] V) = ∑ j, (h (bs j)).smulRight (b j) := by
      apply b.ext; intro k
      simp [LinearMap.smulRight_apply, hbs']
    intro z
    simpa using congrArg (fun F : V →ₗ[K] V => F z) hlin

  haveI : Module.Finite R L := Module.Finite.iff_fg.2 hL.fg
  haveI : Module.Flat R L := by
    rw [IsDedekindDomain.flat_iff_torsion_eq_bot, eq_bot_iff]
    intro x hx
    obtain ⟨a, hax⟩ := (Submodule.mem_torsion_iff x).1 hx
    have ha0 : algebraMap R K (a : R) ≠ 0 :=
      IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors a.2
    have h1 : algebraMap R K (a : R) • (x : V) = 0 := by
      rw [algebraMap_smul]
      have := congrArg Subtype.val hax
      simpa [Submonoid.smul_def] using this
    rw [Submodule.mem_bot]
    exact Subtype.ext ((smul_eq_zero.1 h1).resolve_left ha0)
  haveI : Module.FinitePresentation R L := Module.finitePresentation_of_finite R L
  haveI : Module.Projective R L := Module.Flat.projective_of_finitePresentation
  obtain ⟨n, π, hπ⟩ := Module.Finite.exists_fin' R L
  obtain ⟨sec, hsec⟩ := Module.projective_lifting_property π LinearMap.id hπ
  let g : Fin n → V := fun i => (π (fun j => if i = j then 1 else 0) : V)
  let fi : Fin n → L →ₗ[R] R := fun i => (LinearMap.proj i).comp sec
  have hzL : ∀ z : L, (z : V) = ∑ i, fi i z • g i := by
    intro z
    have h1 : π (sec z) = z := LinearMap.congr_fun hsec z
    calc (z : V) = ((π (sec z) : L) : V) := by rw [h1]
      _ = _ := by rw [LinearMap.pi_apply_eq_sum_univ π (sec z)]; simp [fi, g]

  let w : Fin n → V := fun i => ∑ j, star (algebraMap R K (fi i ⟨b j, hbL j⟩)) • bs j
  have hw_b : ∀ i k, h (w i) (b k) = algebraMap R K (fi i ⟨b k, hbL k⟩) := by
    intro i k
    simp only [w, map_sum, LinearMap.map_smulₛₗ, LinearMap.sum_apply, LinearMap.smul_apply, hbs',
      smul_eq_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    rw [starRingEnd_apply, star_star]
  have hw_L : ∀ i (z : L), h (w i) z = algebraMap R K (fi i z) := by
    intro i z
    obtain ⟨d, hd⟩ :=
      IsLocalization.exist_integer_multiples (nonZeroDivisors R) Finset.univ (fun j => h (bs j) (z : V))
    choose a ha using fun j => hd j (Finset.mem_univ j)
    have hdzV : (d : R) • (z : V) = ∑ j, a j • b j := by
      conv_lhs => rw [hcoord (z : V)]
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [← smul_assoc, ← ha j, algebraMap_smul]
    have hdz : (d : R) • z = ∑ j, a j • (⟨b j, hbL j⟩ : L) := Subtype.ext (by simp [hdzV])
    have hd0 : algebraMap R K (d : R) ≠ 0 :=
      IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors d.2
    have L1 : algebraMap R K d * h (w i) z =
        ∑ j, algebraMap R K (a j) * algebraMap R K (fi i ⟨b j, hbL j⟩) := by
      rw [← smul_eq_mul, ← LinearMap.map_smul, algebraMap_smul, hdzV, map_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [← algebraMap_smul K (a j) (b j), LinearMap.map_smul, hw_b, smul_eq_mul]
    have L2 : algebraMap R K d * algebraMap R K (fi i z) =
        ∑ j, algebraMap R K (a j) * algebraMap R K (fi i ⟨b j, hbL j⟩) := by
      rw [← map_mul, ← smul_eq_mul, ← LinearMap.map_smul, hdz, map_sum, map_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [LinearMap.map_smul, smul_eq_mul, map_mul]
    exact mul_left_cancel₀ hd0 (L1.trans L2.symm)
  refine ⟨n, g, w, fun i => (π _).2, ?_, ?_⟩
  · intro i
    simp only [Formalism.HermitianLatticesTheory.dual, Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap,
      LinearMap.restrictScalars_apply]
    intro y hy
    rw [Submodule.mem_one, ← hs.eq (w i) y, hw_L i ⟨y, hy⟩]
    obtain ⟨r, hr⟩ := hstar (fi i ⟨y, hy⟩)
    exact ⟨r, by rw [hr]; rfl⟩
  · have hlin : (LinearMap.id : V →ₗ[K] V) = ∑ i, (h (w i)).smulRight (g i) := by
      apply LinearMap.ext_on hsp
      intro z hz
      simp only [LinearMap.id_apply, LinearMap.sum_apply, LinearMap.smulRight_apply]
      calc z = ∑ i, fi i ⟨z, hz⟩ • g i := hzL ⟨z, hz⟩
        _ = ∑ i, h (w i) z • g i := Finset.sum_congr rfl fun i _ => by
          rw [show h (w i) z = h (w i) ((⟨z, hz⟩ : L) : V) from rfl, hw_L i ⟨z, hz⟩,
            algebraMap_smul]
    intro z
    simpa using congrArg (fun F : V →ₗ[K] V => F z) hlin
end Formalism.L2.Geo.Def.G1
