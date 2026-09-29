-- Prove2me | solution 1 for Deformation.HondaSystem.exists_mvFormalGroup_basis_coeff_eq_normalForm
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/5a90458a-1af6-5aa0-a8fa-95888a8718ee

import Mathlib
import Definitions.Def_Dieudonne_DatumAndHonda
import Definitions.Def_Dieudonne_WittVectorHom
import Definitions.Def_Dieudonne_WittHomColimit
import Definitions.Def_HopfAlgebra_CartierDual
import Definitions.Def_PDivisibleGroup_Basic
import Definitions.Def_MvFormalGroup_BasicV2
import Definitions.Def_MvFormalGroup_EndRingV2
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_MvFormalGroup_PointsV2
import Theorems.Thm_PDivisibleGroup_exists_mvFormalGroup_ker_eq_span_nthSeries_jointly_injective_surjective_of_isLocalRing_zmodp
import Theorems.Thm_Deformation_HondaSystem_exists_linearMap_surjective_mulVec_isNilpotent_coeff_eq
import Theorems.Thm_Deformation_HondaSystem_exists_basis_isUnit_mulVec_eq_single_of_isNilpotent
import Theorems.Thm_MvFormalGroup_exists_isComm_comp_substAlgHom_of_isUnit_matrix
import Theorems.Thm_Deformation_DieudonneModule_exists_mvPowerSeries_coeff_eq_apply_of_forall_map_eq
import Theorems.Thm_MvPowerSeries_mem_pow_span_X_of_coeff_eq_zero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Deformation_HondaSystem_exists_mvFormalGroup_basis_coeff_eq_normalForm
p2m_attr_erase "instance" "HopfAlgebra.HopfKerHopf.instHopfAlgebra HopfAlgebra.HopfKerHopf.instCoalgebra HopfAlgebra.HopfKerHopf.instIsCocomm HopfAlgebra.HopfKerHopf.instBialgebra HopfAlgebra.IsHopfTower.refl Deformation.UnipotentWittCovector.instInhabited Deformation.UnipotentWittCovector.instAddCommGroup Deformation.TruncWitt.shiftLE_directedSystem Deformation.WittGroup.instAlgebra Deformation.WittGroup.instHopfAlgebra Deformation.WittGroup.instInhabited Deformation.WittGroup.instCommRing Deformation.WittGroup.instBialgebra Deformation.WittGroup.instIsCocomm HopfAlgebra.HopfIdealQuotient.instIsCocomm HopfAlgebra.HopfIdealQuotient.instBialgebra HopfAlgebra.HopfIdealQuotient.instHopfAlgebra Ideal.isHopfIdeal_bot HopfAlgebra.flat_quotient_bot HopfAlgebra.finiteType_quotient CartierDual.instIsCocommViaBialgebra CartierDual.instModuleFreeViaBialgebra CartierDual.instModuleFiniteViaBialgebra"
p2m_attr_erase "simp" "HopfAlgebra.canAlgHom_tmul HopfAlgebra.canMap_tmul HopfAlgebra.HopfKerHopf.ι₂_comulK HopfAlgebra.HopfKerHopf.ι₃_tmul HopfAlgebra.HopfKerHopf.counitK_apply HopfAlgebra.HopfKerHopf.coe_antipodeK HopfAlgebra.HopfKerHopf.ι₂_tmul HopfAlgebra.HopfKerHopf.coe_antipode HopfAlgebra.HopfKerHopf.hopfKerVal_apply HopfAlgebra.HopfKerHopf.valL_apply HopfAlgebra.HopfKerHopf.ι₂_comul HopfAlgebra.HopfTower.quotientMap_mk HopfAlgebra.IsHopfSubalgebra.ι₂_comulK HopfAlgebra.IsHopfTower.toBialgHom_apply HopfAlgebra.IsHopfTower.reprMap_right HopfAlgebra.IsHopfSubalgebra.counitK_apply HopfAlgebra.IsHopfSubalgebra.coe_antipodeK HopfAlgebra.HopfTower.galoisInv_tmul HopfAlgebra.HopfTower.galoisFwd_tmul HopfAlgebra.mem_augIdeal HopfAlgebra.IsHopfTower.reprMap_index HopfAlgebra.HopfTower.antipodeAlgHom_apply HopfAlgebra.IsHopfTower.reprMap_left HopfAlgebra.IsHopfSubalgebra.ι₂_tmul HopfAlgebra.HopfTower.θ₁_tmul HopfAlgebra.HopfTower.fwdB_apply HopfAlgebra.HopfTower.invQuot_mk HopfAlgebra.HopfTower.translateEquiv_apply HopfAlgebra.HopfTower.θ₂_tmul HopfAlgebra.IsHopfSubalgebra.ι₃_tmul Deformation.UnipotentWittCovector.lift_of Deformation.UnipotentWittCovector.of_shift Deformation.UnipotentWittCovector.frobenius_of Deformation.DieudonneModule.toCovector_of Deformation.TruncWitt.frobeniusAddHom_apply Deformation.UnipotentWittCovector.dieudonneDatum_F_apply Deformation.UnipotentWittCovector.map_of Deformation.UnipotentWittCovector.verschiebung_of Deformation.UnipotentWittCovector.dieudonneDatum_V_apply Deformation.DieudonneModule.evalMonoidHom_apply"
p2m_attr_erase "simp" "Deformation.DieudonneModule.eval_of Deformation.UnipotentWittCovector.of_shiftLE Deformation.WittGroup.coe_univHom Deformation.WittGroup.counit_X Deformation.WittGroup.rehom_apply Deformation.WittGroup.lift_X Deformation.WittGroup.antipode_X Deformation.WittGroup.comul_X Deformation.WittGroup.pointsEquiv_symm_apply_X Deformation.WittGroup.coeff_univ HopfAlgebra.HopfIdealQuotient.comul_mk HopfAlgebra.antipodeAlgHom_apply HopfAlgebra.quotientFactorBialgHom_apply_mk HopfAlgebra.quotientBialgHom_apply HopfAlgebra.quotientLiftPoint_mk HopfAlgebra.convCompMonoidHom_apply HopfAlgebra.HopfIdealQuotient.antipode_mk HopfAlgebra.HopfIdealQuotient.counit_mk ModpDieudonneRealization.mk.sizeOf_spec ModpDieudonneRealization.mk.injEq CartierDual.map_apply CartierDual.congr_apply CartierDual.congr_symm_apply CartierDual.pairing_apply CartierDual.mapAlgHom_apply CartierDual.mapLinear_apply"

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 80000
set_option Elab.async false

open scoped TensorProduct
open MvPowerSeries

universe u v w

namespace Deformation
p2m_export "Deformation" "HondaSystem wittHom wittHomShiftLE DieudonneModule DieudonneModule.of DieudonneModule.of_shiftLE DieudonneModule.exists_of DieudonneModule.verschiebung DieudonneModule.frobenius DieudonneModule.map DieudonneModule.map_comp HondaSystem.exists_linearMap_surjective_mulVec_isNilpotent_coeff_eq HondaSystem.exists_basis_isUnit_mulVec_eq_single_of_isNilpotent DieudonneModule.exists_mvPowerSeries_coeff_eq_apply_of_forall_map_eq"
namespace HondaSystem
p2m_export "Deformation.HondaSystem" "L exists_linearMap_surjective_mulVec_isNilpotent_coeff_eq exists_basis_isUnit_mulVec_eq_single_of_isNilpotent"
namespace NormalCoordC2
p2m_open "Deformation.HondaSystem Deformation"

section MatVec

variable {R : Type*} [CommRing R] {d : ℕ} {S : Type*} [AddCommMonoid S] [Module R S]

private def mv (M : Matrix (Fin d) (Fin d) R) (u : Fin d → S) : Fin d → S := fun i => ∑ j, M i j • u j

private theorem mv_apply (M : Matrix (Fin d) (Fin d) R) (u : Fin d → S) (i : Fin d) :
    mv M u i = ∑ j, M i j • u j := rfl

private theorem mv_mv (M N : Matrix (Fin d) (Fin d) R) (u : Fin d → S) : mv M (mv N u) = mv (M * N) u := by
  funext i
  simp only [mv_apply, Matrix.mul_apply, Finset.smul_sum, Finset.sum_smul, smul_smul]
  rw [Finset.sum_comm]

private theorem mv_one (u : Fin d → S) : mv (1 : Matrix (Fin d) (Fin d) R) u = u := by
  funext i
  rw [mv_apply, Finset.sum_eq_single i (fun j _ hj => by rw [Matrix.one_apply_ne (Ne.symm hj), zero_smul])
    (fun h => absurd (Finset.mem_univ i) h), Matrix.one_apply_eq, one_smul]

private theorem map_mv {S' : Type*} [AddCommMonoid S'] [Module R S'] {F : Type*} [FunLike F S S']
    [LinearMapClass F R S S'] (f : F) (M : Matrix (Fin d) (Fin d) R) (u : Fin d → S) (i : Fin d) :
    f (mv M u i) = mv M (fun j => f (u j)) i := by
  simp only [mv_apply, map_sum, map_smul]

end MatVec

section LinSubst

variable {R : Type*} [CommRing R] {d : ℕ} {τ : Type*}

private theorem constantCoeff_mv (M : Matrix (Fin d) (Fin d) R) {u : Fin d → MvPowerSeries τ R}
    (hu : ∀ j, (u j).constantCoeff = 0) (i : Fin d) : (mv M u i).constantCoeff = 0 := by
  rw [mv_apply, map_sum]
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [smul_eq_C_mul, map_mul, hu j, mul_zero]

private theorem subst_mv {τ' : Type*} {a : τ → MvPowerSeries τ' R} (ha : HasSubst a)
    (M : Matrix (Fin d) (Fin d) R) (u : Fin d → MvPowerSeries τ R) (i : Fin d) :
    subst a (mv M u i) = mv M (fun j => subst a (u j)) i := by
  rw [← coe_substAlgHom ha]
  exact map_mv (substAlgHom ha).toLinearMap M u i

private theorem coeff_single_mv (M : Matrix (Fin d) (Fin d) R) (u : Fin d → MvPowerSeries τ R) (t : τ) (i : Fin d) :
    coeff (Finsupp.single t 1) (mv M u i) = ∑ j, M i j * coeff (Finsupp.single t 1) (u j) := by
  rw [map_mv]
  rfl

variable (d) in

private noncomputable def lin (M : Matrix (Fin d) (Fin d) R) : Fin d → MvPowerSeries (Fin d) R :=
  mv M fun j => (X j : MvPowerSeries (Fin d) R)

private theorem lin_apply (M : Matrix (Fin d) (Fin d) R) (i : Fin d) :
    lin d M i = ∑ j, M i j • (X j : MvPowerSeries (Fin d) R) := rfl

private theorem constantCoeff_lin (M : Matrix (Fin d) (Fin d) R) (i : Fin d) : (lin d M i).constantCoeff = 0 :=
  constantCoeff_mv M (fun j => constantCoeff_X j) i

private theorem hasSubst_lin (M : Matrix (Fin d) (Fin d) R) : HasSubst (lin d M) :=
  hasSubst_of_constantCoeff_zero (constantCoeff_lin M)

private theorem subst_lin_apply {a : Fin d → MvPowerSeries τ R} (ha : HasSubst a) (M : Matrix (Fin d) (Fin d) R)
    (i : Fin d) : subst a (lin d M i) = mv M a i := by
  rw [lin, subst_mv ha]
  congr 1
  funext j
  exact subst_X ha j

private theorem subst_lin_lin (M N : Matrix (Fin d) (Fin d) R) (i : Fin d) :
    subst (lin d N) (lin d M i) = lin d (M * N) i := by
  rw [subst_lin_apply (hasSubst_lin N), lin, lin, mv_mv]

variable {P Q : Matrix (Fin d) (Fin d) R}

private theorem subst_lin_lin_of_mul_eq_one (h : P * Q = 1) (i : Fin d) :
    subst (lin d Q) (lin d P i) = X i := by
  rw [subst_lin_lin, h, lin, mv_one]

private theorem subst_lin_subst_lin (h : P * Q = 1) (F : MvPowerSeries (Fin d) R) :
    subst (lin d Q) (subst (lin d P) F) = F := by
  rw [subst_comp_subst_apply (hasSubst_lin P) (hasSubst_lin Q)]
  have : (fun s => subst (lin d Q) (lin d P s)) = fun s => (X s : MvPowerSeries (Fin d) R) :=
    funext fun s => subst_lin_lin_of_mul_eq_one h s
  rw [this, subst_self]
  rfl

private theorem span_range_mv (hQP : Q * P = 1) (f : Fin d → MvPowerSeries τ R) :
    Ideal.span (Set.range (mv P f)) = Ideal.span (Set.range f) := by
  apply le_antisymm
  · rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    rw [SetLike.mem_coe, mv_apply]
    exact Ideal.sum_mem _ fun j _ => by
      rw [smul_eq_C_mul]; exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨j, rfl⟩)
  · rw [Ideal.span_le]
    rintro _ ⟨j, rfl⟩
    have hf : f j = mv Q (mv P f) j := by rw [mv_mv, hQP, mv_one]
    rw [SetLike.mem_coe, hf, mv_apply]
    exact Ideal.sum_mem _ fun i _ => by
      rw [smul_eq_C_mul]; exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨i, rfl⟩)

end LinSubst

section NthSeries

variable {R : Type*} [CommRing R] {d : ℕ}

private theorem nthSeries_mem_pow_two (Φ : MvFormalGroup d R) (n : ℕ) (hn : (n : R) = 0) (i : Fin d) :
    Φ.nthSeries n i ∈ Ideal.span (Set.range (X : Fin d → MvPowerSeries (Fin d) R)) ^ 2 := by
  classical
  refine MvPowerSeries.mem_pow_span_X_of_coeff_eq_zero 2 _ fun m hm => ?_
  rcases Nat.lt_or_ge m.degree 1 with h0 | h1
  · have hm0 : m = 0 := (Finsupp.degree_eq_zero_iff m).mp (by omega)
    subst hm0
    rw [MvPowerSeries.coeff_zero_eq_constantCoeff_apply]
    exact MvFormalGroup.constantCoeff_nthSeries Φ n i
  · have hdeg : m.degree = 1 := by omega
    obtain ⟨j, rfl⟩ : ∃ j, Finsupp.single j 1 = m := by
      have hmem : m ∈ {d' : Fin d →₀ ℕ | d'.degree = 1} := hdeg
      rw [← Finsupp.range_single_one] at hmem
      exact hmem
    have h := congrFun (congrFun (MvFormalGroup.linearPart_nthSeries Φ n) i) j
    change coeff (Finsupp.single j 1) (Φ.nthSeries n i) = _ at h
    rw [h, Matrix.smul_apply, Matrix.one_apply, nsmul_eq_mul, hn, zero_mul]

end NthSeries

end Deformation.HondaSystem.NormalCoordC2

open Deformation.HondaSystem.NormalCoordC2 in

theorem solution
    {𝓞 : Type u} [CommRing 𝓞] (p : ℕ) [Fact p.Prime] (hp : (p : 𝓞) ∈ nonZeroDivisors 𝓞)
    [Algebra 𝓞 (ZMod p)] (hker : RingHom.ker (algebraMap 𝓞 (ZMod p)) = Ideal.span {(p : 𝓞)})
    [IsAdicComplete (Ideal.span {(p : 𝓞)}) 𝓞]
    (r : ℕ) (H₁ : Deformation.HondaSystem (p : 𝓞) (Fin r → 𝓞))
    (G : ℕ → Type v) [∀ v, CommRing (G v)] [∀ v, HopfAlgebra (ZMod p) (G v)]
    [∀ v, Coalgebra.IsCocomm (ZMod p) (G v)] [∀ v, Module.Finite (ZMod p) (G v)]
    (s : ∀ v, G (v + 1) →ₐc[ZMod p] G v) (hs : ∀ v, Function.Surjective (s v))
    (hrankG : ∀ v, Module.finrank (ZMod p) (G v) = p ^ (v * r))
    (hkerG : ∀ v, RingHom.ker (s v) = PDivisibleGroup.Hopf.torsionIdeal (ZMod p) (G (v + 1)) (p ^ v))
    (hunipG : ∀ v, IsLocalRing (CartierDual (ZMod p) (G v)))
    (π : ∀ v, (Fin r → 𝓞) →+ Deformation.DieudonneModule (ZMod p) p (G v))
    (hπ : ∀ v, Function.Surjective (π v))
    (hπker : ∀ v x, π v x = 0 ↔ ∃ y, x = (p : 𝓞) ^ v • y)
    (hπF : ∀ v x, π v (H₁.F x) = Deformation.DieudonneModule.frobenius (ZMod p) p (G v) (π v x))
    (hπV : ∀ v x, π v (H₁.V x) = Deformation.DieudonneModule.verschiebung (ZMod p) p (G v) (π v x))
    (hπs : ∀ v x, Deformation.DieudonneModule.map (ZMod p) p (s v) (π (v + 1) x) = π v x)
    (hc : ℕ)
    (Gc : ℕ → Type v) [∀ v, CommRing (Gc v)] [∀ v, HopfAlgebra (ZMod p) (Gc v)]
    [∀ v, Coalgebra.IsCocomm (ZMod p) (Gc v)] [∀ v, Module.Finite (ZMod p) (Gc v)]
    (Ge : ℕ → Type v) [∀ v, CommRing (Ge v)] [∀ v, HopfAlgebra (ZMod p) (Ge v)]
    [∀ v, Coalgebra.IsCocomm (ZMod p) (Ge v)] [∀ v, Module.Finite (ZMod p) (Ge v)]
    (sc : ∀ v, Gc (v + 1) →ₐc[ZMod p] Gc v)
    (qc : ∀ v, G v →ₐc[ZMod p] Gc v) (πe : ∀ v, G v →ₐc[ZMod p] Ge v)
    (Θ : ∀ v, G v →ₐc[ZMod p] Gc v ⊗[ZMod p] Ge v)
    (hGc : ∀ v, IsLocalRing (Gc v)) (hGe : ∀ v, IsReduced (Ge v))
    (hsc : ∀ v, Function.Surjective (sc v))
    (hrankGc : ∀ v, Module.finrank (ZMod p) (Gc v) = p ^ (v * hc))
    (hkerGc : ∀ v, RingHom.ker (sc v) = PDivisibleGroup.Hopf.torsionIdeal (ZMod p) (Gc (v + 1)) (p ^ v))
    (hqc : ∀ v, Function.Surjective (qc v))
    (hΘ : ∀ v, Function.Bijective (Θ v))
    (hΘapply : ∀ v b, Θ v b = Algebra.TensorProduct.map (qc v : G v →ₐ[ZMod p] Gc v)
      (πe v : G v →ₐ[ZMod p] Ge v) (Coalgebra.comul (R := ZMod p) b))
    (hqcs : ∀ v, (qc v).comp (s v) = (sc v).comp (qc (v + 1)))
    :
    ∃ (d : ℕ) (Φ : MvFormalGroup d (ZMod p)) (_ : Φ.IsComm)
      (κ : ∀ v, MvPowerSeries (Fin d) (ZMod p) →ₐ[ZMod p] Gc v)
      (b : Module.Basis (Fin d) 𝓞 H₁.L)
      (abar : Fin d → ℕ → MvPowerSeries (Fin d) (ZMod p)),

      (∀ v, Function.Surjective (κ v)) ∧
      (∀ v, RingHom.ker (κ v) = Ideal.span (Set.range (Φ.nthSeries (p ^ v)))) ∧
      (∀ v, (sc v : Gc (v + 1) →ₐ[ZMod p] Gc v).comp (κ (v + 1)) = κ v) ∧
      (∀ v i, Coalgebra.counit (R := ZMod p) (κ v (X i)) = 0) ∧
      (∀ v i, κ v (X i) ∈ (Ideal.span {(p : Gc v)}).radical) ∧
      (∀ v F, κ v F = MvFormalGroup.adicEval (Ideal.span {(p : Gc v)}) (fun i => κ v (X i)) F) ∧
      (∀ v i, Coalgebra.comul (R := ZMod p) (κ v (X i)) =
        MvFormalGroup.adicEval (Ideal.span {(p : Gc v ⊗[ZMod p] Gc v)})
          (Sum.elim (fun j => κ v (X j) ⊗ₜ[ZMod p] (1 : Gc v)) (fun j => (1 : Gc v) ⊗ₜ[ZMod p] κ v (X j)))
          (Φ.toPowerSeries i)) ∧
      Module.finrank (ZMod p)
        (MvPowerSeries (Fin d) (ZMod p) ⧸ Ideal.span (Set.range (Φ.nthSeries p))) = p ^ hc ∧
      d = Module.finrank (ZMod p) (PDivisibleGroup.Hopf.augIdeal (ZMod p) (Gc 1)).Cotangent ∧
      (∀ N : ℕ, ∃ v, RingHom.ker (κ v) ≤
        (Ideal.span (Set.range (X : Fin d → MvPowerSeries (Fin d) (ZMod p)))) ^ N) ∧
      (∀ F, (∀ v, κ v F = 0) → F = 0) ∧
      (∀ z : ∀ v, Gc v, (∀ v, sc v (z (v + 1)) = z v) → ∃ F, ∀ v, κ v F = z v) ∧

      (∀ i k, MvPowerSeries.constantCoeff (abar i k) = 0) ∧
      (∀ i (N : ℕ), ∃ k₀, ∀ k, k₀ ≤ k →
        abar i k ∈ (Ideal.span (Set.range (X : Fin d → MvPowerSeries (Fin d) (ZMod p)))) ^ N) ∧
      (∀ i (v n : ℕ) (u : Deformation.wittHom (ZMod p) p n (Gc v)),
        Deformation.DieudonneModule.of (ZMod p) p (Gc v) n u =
          Deformation.DieudonneModule.map (ZMod p) p (qc v) (π v ((b i : H₁.L) : Fin r → 𝓞)) →
        ∀ (k : ℕ) (hk : k < n),
          (u : TruncatedWittVector p n (Gc v)).coeff ⟨n - 1 - k, by omega⟩ = κ v (abar i k)) ∧

      (∀ i j : Fin d, MvPowerSeries.coeff (Finsupp.single j 1) (abar i 0) = if i = j then 1 else 0) ∧
      (∀ i j : Fin d, j ≤ i → MvPowerSeries.coeff (Finsupp.single j 1) (abar i 1) = 0) := by
  classical

  obtain ⟨d, Φ, hΦc, κ, hκsurj, hκker, hκs, hκε, hκrad, hκeval, hκΔ, hheight, hd, hκkerN, hκinj, hκsurjj⟩ :=
    PDivisibleGroup.exists_mvFormalGroup_ker_eq_span_nthSeries_jointly_injective_surjective_of_isLocalRing_zmodp
      p hc Gc sc hsc hrankGc hkerGc hGc
  haveI : Φ.IsComm := hΦc

  have hκ1ker : RingHom.ker (κ 1) ≤
      Ideal.span (Set.range (X : Fin d → MvPowerSeries (Fin d) (ZMod p))) ^ 2 := by
    rw [hκker 1, Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    exact nthSeries_mem_pow_two Φ (p ^ 1) (by rw [pow_one, ZMod.natCast_self]) i

  obtain ⟨lam₀, lam₁, C, hfree, hfin, hrankL, hlsurj, hlker, hCnil, hlam₁, hchar0, hchar1⟩ :=
    Deformation.HondaSystem.exists_linearMap_surjective_mulVec_isNilpotent_coeff_eq p hp hker r H₁ G s hs hrankG
      hkerG hunipG π hπ hπker hπF hπV hπs (Gc 1) (Ge 1) (qc 1) (πe 1) (Θ 1) (hGc 1) (hGe 1) (hqc 1) (hΘ 1)
      (hΘapply 1) (κ 1) (hκsurj 1) (hκε 1) hκ1ker hd
  haveI : Module.Free 𝓞 H₁.L := hfree
  haveI : Module.Finite 𝓞 H₁.L := hfin

  obtain ⟨b, P, hPu, hP0, hP1⟩ :=
    Deformation.HondaSystem.exists_basis_isUnit_mulVec_eq_single_of_isNilpotent p hp hker H₁.L hrankL lam₀ lam₁
      hlsurj hlker C hCnil hlam₁

  set Pb : Matrix (Fin d) (Fin d) (ZMod p) := P.map (algebraMap 𝓞 (ZMod p)) with hPb
  have hPbu : IsUnit Pb := by
    have h := hPu.map (algebraMap 𝓞 (ZMod p)).mapMatrix
    rwa [RingHom.mapMatrix_apply] at h
  have hPbdet : IsUnit Pb.det := (Matrix.isUnit_iff_isUnit_det Pb).mp hPbu
  have hmulinv : Pb * Pb⁻¹ = 1 := Matrix.mul_nonsing_inv Pb hPbdet
  have hinvmul : Pb⁻¹ * Pb = 1 := Matrix.nonsing_inv_mul Pb hPbdet
  set Pm : Matrix (Fin d) (Fin d) (ZMod p) := Pb⁻¹.transpose with hPm
  set Qm : Matrix (Fin d) (Fin d) (ZMod p) := Pb.transpose with hQm
  have hPQ : Pm * Qm = 1 := by
    rw [hPm, hQm, ← Matrix.transpose_mul, hmulinv, Matrix.transpose_one]
  have hQP : Qm * Pm = 1 := by
    rw [hPm, hQm, ← Matrix.transpose_mul, hinvmul, Matrix.transpose_one]
  have hPmu : IsUnit Pm := ⟨⟨Pm, Qm, hPQ, hQP⟩, rfl⟩

  obtain ⟨Φ', hΦ'c, ℓ, κ', hℓ, hκ', hκ'surj, hκ'ker, hκ's, hκ'ε, hκ'rad, hκ'eval, hκ'Δ, hheight'⟩ :=
    MvFormalGroup.exists_isComm_comp_substAlgHom_of_isUnit_matrix p Gc sc Φ κ hκsurj hκker hκs hκε hκrad hκeval
      hκΔ Pm hPmu
  have hℓlin : ℓ.toPowerSeries = lin d Pm := hℓ
  have hκ'' : ∀ v F, κ' v F = κ v (subst (lin d Pm) F) := fun v F => by rw [hκ', hℓlin]
  have hback : ∀ F : MvPowerSeries (Fin d) (ZMod p), subst (lin d Qm) (subst (lin d Pm) F) = F :=
    subst_lin_subst_lin hPQ
  have hforth : ∀ F : MvPowerSeries (Fin d) (ZMod p), subst (lin d Pm) (subst (lin d Qm) F) = F :=
    subst_lin_subst_lin hQP

  have hIpow : ∀ (N : ℕ) (F : MvPowerSeries (Fin d) (ZMod p)),
      F ∈ Ideal.span (Set.range (X : Fin d → MvPowerSeries (Fin d) (ZMod p))) ^ N →
      subst (lin d Qm) F ∈ Ideal.span (Set.range (X : Fin d → MvPowerSeries (Fin d) (ZMod p))) ^ N := by
    intro N F hF
    have hmem := Ideal.mem_map_of_mem (substAlgHom (hasSubst_lin Qm)) hF
    rw [Ideal.map_pow, Ideal.map_span, ← Set.range_comp] at hmem
    have hrange : (⇑(substAlgHom (hasSubst_lin Qm)) ∘ (X : Fin d → MvPowerSeries (Fin d) (ZMod p))) =
        lin d Qm := by
      funext j
      show substAlgHom (hasSubst_lin Qm) (X j) = lin d Qm j
      rw [coe_substAlgHom]
      exact subst_X (hasSubst_lin Qm) j
    have hspan : Ideal.span (Set.range (lin d Qm)) =
        Ideal.span (Set.range (X : Fin d → MvPowerSeries (Fin d) (ZMod p))) := span_range_mv hPQ _
    rw [hrange, hspan] at hmem
    rw [← coe_substAlgHom (hasSubst_lin Qm)]
    exact hmem

  have h10 : ∀ N : ℕ, ∃ v, RingHom.ker (κ' v) ≤
      Ideal.span (Set.range (X : Fin d → MvPowerSeries (Fin d) (ZMod p))) ^ N := by
    intro N
    obtain ⟨v, hv⟩ := hκkerN N
    refine ⟨v, fun F hF => ?_⟩
    have h1 : subst (lin d Pm) F ∈ RingHom.ker (κ v) := by
      rw [RingHom.mem_ker, ← hκ'']; exact hF
    have h2 := hIpow N _ (hv h1)
    rwa [hback] at h2
  have h11 : ∀ F, (∀ v, κ' v F = 0) → F = 0 := by
    intro F hF
    have h0 : subst (lin d Pm) F = 0 := hκinj _ fun v => by rw [← hκ'']; exact hF v
    rw [← hback F, h0, ← coe_substAlgHom (hasSubst_lin Qm), map_zero]
  have h12 : ∀ z : ∀ v, Gc v, (∀ v, sc v (z (v + 1)) = z v) → ∃ F, ∀ v, κ' v F = z v := by
    intro z hz
    obtain ⟨F, hF⟩ := hκsurjj z hz
    exact ⟨subst (lin d Qm) F, fun v => by rw [hκ'', hforth, hF]⟩
  have h8 : Module.finrank (ZMod p)
      (MvPowerSeries (Fin d) (ZMod p) ⧸ Ideal.span (Set.range (Φ'.nthSeries p))) = p ^ hc :=
    hheight'.trans hheight

  have hm : ∀ (i : Fin d) (v : ℕ),
      Deformation.DieudonneModule.map (ZMod p) p (sc v)
          (Deformation.DieudonneModule.map (ZMod p) p (qc (v + 1)) (π (v + 1) ((b i : H₁.L) : Fin r → 𝓞))) =
        Deformation.DieudonneModule.map (ZMod p) p (qc v) (π v ((b i : H₁.L) : Fin r → 𝓞)) := by
    intro i v
    rw [← Deformation.DieudonneModule.map_comp, ← hqcs v, Deformation.DieudonneModule.map_comp, hπs]
  choose abar habar0 habarN habar _huniq using fun i : Fin d =>
    Deformation.DieudonneModule.exists_mvPowerSeries_coeff_eq_apply_of_forall_map_eq p Gc sc κ' hκ's hκ'ε h11 h12
      h10 (fun v => Deformation.DieudonneModule.map (ZMod p) p (qc v) (π v ((b i : H₁.L) : Fin r → 𝓞))) (hm i)

  have hcoefX : ∀ a t : Fin d, coeff (Finsupp.single t 1) (X a : MvPowerSeries (Fin d) (ZMod p)) =
      (1 : Matrix (Fin d) (Fin d) (ZMod p)) a t := fun a t =>
    congrFun (congrFun (MvFormalGroup.linearPart_X (g := d) (R := ZMod p)) a) t
  have hcoeflin : ∀ s t : Fin d, coeff (Finsupp.single t 1) (lin d Pm s) = Pb⁻¹ t s := by
    intro s t
    rw [lin, coeff_single_mv]
    simp_rw [hcoefX]
    rw [← Matrix.mul_apply, Matrix.mul_one, hPm, Matrix.transpose_apply]
  have hchain : ∀ (g : MvPowerSeries (Fin d) (ZMod p)) (t : Fin d),
      coeff (Finsupp.single t 1) (subst (lin d Pm) g) =
        Pb⁻¹.mulVec (fun s => coeff (Finsupp.single s 1) g) t := by
    intro g t
    rw [MvFormalGroup.coeff_single_subst (constantCoeff_lin Pm) g t, Matrix.mulVec, dotProduct]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [hcoeflin, mul_comm]
  have hsolve : ∀ (g : MvPowerSeries (Fin d) (ZMod p)) (w : Fin d → ZMod p),
      (∀ t, coeff (Finsupp.single t 1) (subst (lin d Pm) g) = w t) →
      ∀ j, coeff (Finsupp.single j 1) g = Pb.mulVec w j := by
    intro g w hw j
    have hvec : Pb⁻¹.mulVec (fun s => coeff (Finsupp.single s 1) g) = w :=
      funext fun t => (hchain g t).symm.trans (hw t)
    have hg : (fun s => coeff (Finsupp.single s 1) g) = Pb.mulVec w := by
      rw [← hvec, Matrix.mulVec_mulVec, hmulinv, Matrix.one_mulVec]
    exact congrFun hg j
  have hconst : ∀ i k, constantCoeff (subst (lin d Pm) (abar i k)) = 0 := fun i k =>
    constantCoeff_subst_eq_zero (hasSubst_lin Pm) (constantCoeff_lin Pm) (habar0 i k)

  refine ⟨d, Φ', hΦ'c, κ', b, abar, hκ'surj, hκ'ker, hκ's, hκ'ε, hκ'rad, hκ'eval, hκ'Δ, h8, hd, h10, h11, h12,
    habar0, habarN, habar, ?_, ?_⟩
  ·
    intro i j
    obtain ⟨n, x, hx⟩ := Deformation.DieudonneModule.exists_of
      (Deformation.DieudonneModule.map (ZMod p) p (qc 1) (π 1 ((b i : H₁.L) : Fin r → 𝓞)))
    set u := Deformation.wittHomShiftLE (ZMod p) p (Gc 1) (Nat.le_add_right n 1) x with hu_def
    have hu : Deformation.DieudonneModule.of (ZMod p) p (Gc 1) (n + 1) u =
        Deformation.DieudonneModule.map (ZMod p) p (qc 1) (π 1 ((b i : H₁.L) : Fin r → 𝓞)) := by
      rw [hu_def, Deformation.DieudonneModule.of_shiftLE, hx]
    have hS6 := habar i 1 (n + 1) u hu 0 (by omega)
    have hlast : κ 1 (subst (lin d Pm) (abar i 0)) =
        (u : TruncatedWittVector p (n + 1) (Gc 1)).coeff (Fin.last n) := by
      rw [← hκ'']
      have e : (Fin.last n : Fin (n + 1)) = ⟨n + 1 - 1 - 0, by omega⟩ := Fin.ext (by simp)
      rw [e]
      exact hS6.symm
    have hH := hchar0 (b i) n u hu (subst (lin d Pm) (abar i 0)) (hconst i 0) hlast
    rw [hsolve (abar i 0) (lam₀ (b i)) hH j, hP0 i, Pi.single_apply]
    by_cases hij : i = j
    · subst hij
      simp
    · rw [if_neg (Ne.symm hij), if_neg hij]
  ·
    intro i j hji
    obtain ⟨n, x, hx⟩ := Deformation.DieudonneModule.exists_of
      (Deformation.DieudonneModule.map (ZMod p) p (qc 1) (π 1 ((b i : H₁.L) : Fin r → 𝓞)))
    set u := Deformation.wittHomShiftLE (ZMod p) p (Gc 1) (Nat.le_add_right n 2) x with hu_def
    have hu : Deformation.DieudonneModule.of (ZMod p) p (Gc 1) (n + 2) u =
        Deformation.DieudonneModule.map (ZMod p) p (qc 1) (π 1 ((b i : H₁.L) : Fin r → 𝓞)) := by
      rw [hu_def, Deformation.DieudonneModule.of_shiftLE, hx]
    have hS6 := habar i 1 (n + 2) u hu 1 (by omega)
    have hn : κ 1 (subst (lin d Pm) (abar i 1)) =
        (u : TruncatedWittVector p (n + 2) (Gc 1)).coeff ⟨n, by omega⟩ := by
      rw [← hκ'']
      have e : (⟨n, by omega⟩ : Fin (n + 2)) = ⟨n + 2 - 1 - 1, by omega⟩ := Fin.ext (by simp)
      rw [e]
      exact hS6.symm
    have hH := hchar1 (b i) n u hu (subst (lin d Pm) (abar i 1)) (hconst i 1) hn
    rw [hsolve (abar i 1) (lam₁ (b i)) hH j]
    exact hP1 i j hji

end S_Deformation_HondaSystem_exists_mvFormalGroup_basis_coeff_eq_normalForm
end P2MW
export P2MW.S_Deformation_HondaSystem_exists_mvFormalGroup_basis_coeff_eq_normalForm (solution)
