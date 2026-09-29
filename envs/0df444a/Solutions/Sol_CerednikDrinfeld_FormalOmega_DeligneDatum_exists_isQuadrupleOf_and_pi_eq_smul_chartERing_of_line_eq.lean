-- Prove2me | solution 1 for CerednikDrinfeld.FormalOmega.DeligneDatum.exists_isQuadrupleOf_and_pi_eq_smul_chartERing_of_line_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/9fcf1007-91a3-5e6f-ad9a-ef54d43281bc

import Mathlib
import Definitions.Def_CerednikDrinfeld_DrinfeldQuadruple
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneFunctor
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneChartRings
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlanePoints
import Theorems.Thm_CerednikDrinfeld_FormalOmega_exists_act_stdFullLattice_eq_and_act_act_eq_of_lt_of_lt
import Theorems.Thm_CerednikDrinfeld_FormalOmega_DeligneDatum_inEdgeChart_act_scalarGL_inv_of_inEdgeChart
import Theorems.Thm_Module_isClosed_setOf_range_le_smul_top
import Theorems.Thm_Module_Invertible_bijective_localizedModule_map_of_not_range_le
import Theorems.Thm_Module_Invertible_range_le_smul_top_or_of_comp_eq_smul
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_FormalOmega_DeligneDatum_exists_isQuadrupleOf_and_pi_eq_smul_chartERing_of_line_eq

set_option autoImplicit false

open scoped TensorProduct
open LT.LatticeTree CerednikDrinfeld CerednikDrinfeld.FormalOmega

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace X2Body

variable {𝒪 : Type} [CommRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K]
variable {B : Type} [CommRing B] [Algebra 𝒪 B]

noncomputable def stalkQuot (x : PrimeSpectrum B) (L : FullLattice 𝒪 K) (N : Submodule B (latticeBaseChange 𝒪 K B L)) :
    latticeBaseChange 𝒪 K (locRing B x) L →ₗ[locRing B x] stalk B x (latticeBaseChange 𝒪 K B L ⧸ N) :=
  (IsLocalizedModule.isBaseChange x.asIdeal.primeCompl (locRing B x)
      (LocalizedModule.mkLinearMap x.asIdeal.primeCompl (latticeBaseChange 𝒪 K B L ⧸ N))).equiv.toLinearMap
    ∘ₗ Module.Grassmannian.baseChangeMkQ (locRing B x) N

theorem ker_stalkQuot (x : PrimeSpectrum B) (L : FullLattice 𝒪 K) (N : Submodule B (latticeBaseChange 𝒪 K B L)) :
    LinearMap.ker (stalkQuot x L N) = lineBaseChange (toLocRing B x) L N := by
  rw [stalkQuot, LinearMap.ker_comp, LinearEquiv.ker, Submodule.comap_bot,
    lineBaseChange_eq_ker (toLocRing B x) (fun _ => rfl) L N]

theorem stalkQuot_surjective (x : PrimeSpectrum B) (L : FullLattice 𝒪 K) (N : Submodule B (latticeBaseChange 𝒪 K B L)) :
    Function.Surjective (stalkQuot x L N) := by
  rw [stalkQuot, LinearMap.coe_comp]
  refine (LinearEquiv.surjective _).comp ?_
  show Function.Surjective (Module.Grassmannian.baseChangeMkQ (locRing B x) N)
  unfold Module.Grassmannian.baseChangeMkQ
  rw [LinearMap.coe_comp]
  refine Function.Surjective.comp ?_ (LinearEquiv.surjective _)
  rw [LinearMap.baseChange_eq_ltensor]
  exact LinearMap.lTensor_surjective _ (Submodule.mkQ_surjective N)

theorem stalkQuot_one_tmul (x : PrimeSpectrum B) (L : FullLattice 𝒪 K) (N : Submodule B (latticeBaseChange 𝒪 K B L))
    (v : ↥L.1) :
    stalkQuot x L N ((1 : locRing B x) ⊗ₜ[𝒪] v) =
      LocalizedModule.mkLinearMap x.asIdeal.primeCompl _ (N.mkQ ((1 : B) ⊗ₜ[𝒪] v)) := by
  rw [stalkQuot, LinearMap.comp_apply, LinearEquiv.coe_coe]
  unfold Module.Grassmannian.baseChangeMkQ
  rw [LinearMap.comp_apply, LinearEquiv.coe_coe, TensorProduct.AlgebraTensorModule.cancelBaseChange_symm_tmul,
    LinearMap.baseChange_tmul, IsBaseChange.equiv_tmul, one_smul, Submodule.mkQ_apply]

section NotMem
variable {B : Type} [CommRing B]

theorem mem_smul_top_of_forall_form {P : Type} [AddCommGroup P] [Module B P] [Module.Projective B P]
    (I : Ideal B) (t : P) (h : ∀ φ : P →ₗ[B] B, φ t ∈ I) : t ∈ I • (⊤ : Submodule B P) := by
  classical
  obtain ⟨s, hs⟩ := Module.Projective.out (R := B) (P := P)
  have ht : t = Finsupp.linearCombination B (id : P → P) (s t) := (hs t).symm
  rw [ht, Finsupp.linearCombination_apply]
  refine Submodule.sum_mem _ fun p _ => ?_
  refine Submodule.smul_mem_smul (h ((Finsupp.lapply p) ∘ₗ s)) Submodule.mem_top

theorem mem_of_mk_mem_smul_top (x : PrimeSpectrum B) (b : B)
    (hb : (LocalizedModule.mk b 1 : LocalizedModule x.asIdeal.primeCompl B) ∈
      x.asIdeal • (⊤ : Submodule B (LocalizedModule x.asIdeal.primeCompl B))) : b ∈ x.asIdeal := by

  have key : ∀ w : LocalizedModule x.asIdeal.primeCompl B, w ∈ x.asIdeal • (⊤ : Submodule B _) →
      ∃ (b' : B) (s : x.asIdeal.primeCompl), b' ∈ x.asIdeal ∧ w = LocalizedModule.mk b' s := by
    intro w hw
    refine Submodule.smul_induction_on hw ?_ ?_
    · intro r hr n _
      induction n using LocalizedModule.induction_on with
      | h c s => exact ⟨r * c, s, x.asIdeal.mul_mem_right c hr, by rw [LocalizedModule.smul'_mk, smul_eq_mul]⟩
    · rintro w₁ w₂ ⟨b₁, s₁, h₁, rfl⟩ ⟨b₂, s₂, h₂, rfl⟩
      refine ⟨(s₂ : B) * b₁ + (s₁ : B) * b₂, s₁ * s₂, x.asIdeal.add_mem (x.asIdeal.mul_mem_left _ h₁)
        (x.asIdeal.mul_mem_left _ h₂), ?_⟩
      rw [LocalizedModule.mk_add_mk]
      simp only [Submonoid.smul_def, smul_eq_mul]
  obtain ⟨b', s, hb', he⟩ := key _ hb
  rw [LocalizedModule.mk_eq] at he
  obtain ⟨u, hu⟩ := he
  simp only [Submonoid.smul_def, smul_eq_mul, OneMemClass.coe_one, one_mul, mul_one] at hu

  have : (u : B) * ((s : B) * b) ∈ x.asIdeal := by rw [hu]; exact x.asIdeal.mul_mem_left _ hb'
  rcases x.isPrime.mem_or_mem this with h | h
  · exact absurd h u.2
  · rcases x.isPrime.mem_or_mem h with h | h
    · exact absurd h s.2
    · exact h

end NotMem

section Chart

variable [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] [IsFractionRing 𝒪 K] {π : 𝒪}
variable {M' M : FullLattice 𝒪 K} (d : DeligneDatum (K := K) π B)

abbrev T0 (M' : FullLattice 𝒪 K) : Type := latticeBaseChange 𝒪 K B M' ⧸ d.line M'

abbrev T1 (M : FullLattice 𝒪 K) : Type := latticeBaseChange 𝒪 K B M ⧸ d.line M

scoped instance instInvertibleT0 (M' : FullLattice 𝒪 K) : Module.Invertible B (T0 d M') := d.invertible M'

noncomputable def Pi0 (hle : M'.1 ≤ M.1) : T0 d M' →ₗ[B] T1 d M :=
  Submodule.mapQ _ _ (inclBaseChange B hle) (Submodule.map_le_iff_le_comap.mp (d.mono hle))

theorem hπK_of_irreducible (hπ : Irreducible π) : algebraMap 𝒪 K π ≠ 0 :=
  (map_ne_zero_iff (algebraMap 𝒪 K) (IsFractionRing.injective 𝒪 K)).mpr hπ.ne_zero

noncomputable def piUnit (hπ : Irreducible π) : Kˣ := Units.mk0 _ (hπK_of_irreducible (K := K) hπ)

theorem act_piUnit_le (hπ : Irreducible π) (hπM : ∀ v ∈ M.1, algebraMap 𝒪 K π • v ∈ M'.1) :
    (FullLattice.act (scalarGL (piUnit (K := K) hπ)) M).1 ≤ M'.1 := by
  intro v hv
  obtain ⟨w, hw, rfl⟩ := mem_latticeMap_scalarGL.mp hv
  exact hπM w hw

theorem smulInto_baseChange_eq (hπ : Irreducible π) (hπM : ∀ v ∈ M.1, algebraMap 𝒪 K π • v ∈ M'.1) :
    ((smulInto π hπM).baseChange B : latticeBaseChange 𝒪 K B M →ₗ[B] latticeBaseChange 𝒪 K B M') =
      (inclBaseChange B (act_piUnit_le hπ hπM)) ∘ₗ (actBaseChange B (scalarGL (piUnit (K := K) hπ)) M).toLinearMap := by
  refine TensorProduct.AlgebraTensorModule.ext fun b v => ?_
  rw [LinearMap.baseChange_tmul, LinearMap.comp_apply, LinearEquiv.coe_coe]
  change _ = inclBaseChange B (act_piUnit_le hπ hπM)
    (((latticeMapEquiv (scalarGL (piUnit (K := K) hπ)) M.1).baseChange 𝒪 B _ _) (b ⊗ₜ[𝒪] v))
  rw [LinearEquiv.baseChange_tmul, inclBaseChange]
  erw [LinearMap.baseChange_tmul]
  congr 1
  apply Subtype.ext
  rw [coe_smulInto_apply, Submodule.coe_inclusion]
  change algebraMap 𝒪 K π • (v : Fin 2 → K) =
    Matrix.mulVec ((scalarGL (piUnit (K := K) hπ) : Matrix.GeneralLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)
      (v : Fin 2 → K)
  rw [scalarGL_mulVec]
  rfl

theorem map_smulInto_le (hπ : Irreducible π) (hπM : ∀ v ∈ M.1, algebraMap 𝒪 K π • v ∈ M'.1) :
    (d.line M).map ((smulInto π hπM).baseChange B :
      latticeBaseChange 𝒪 K B M →ₗ[B] latticeBaseChange 𝒪 K B M') ≤ d.line M' := by
  rw [smulInto_baseChange_eq hπ hπM, Submodule.map_comp, ← d.homothety (piUnit (K := K) hπ) M]
  exact d.mono (act_piUnit_le hπ hπM)

noncomputable def Pi1 (hπ : Irreducible π) (hπM : ∀ v ∈ M.1, algebraMap 𝒪 K π • v ∈ M'.1) :
    T1 d M →ₗ[B] T0 d M' :=
  Submodule.mapQ _ _ ((smulInto π hπM).baseChange B) (Submodule.map_le_iff_le_comap.mp (map_smulInto_le d hπ hπM))

theorem smul_incl_apply (hle : M'.1 ≤ M.1) (hπM : ∀ v ∈ M.1, algebraMap 𝒪 K π • v ∈ M'.1)
    (y : latticeBaseChange 𝒪 K B M') :
    ((smulInto π hπM).baseChange B) (inclBaseChange B hle y) = algebraMap 𝒪 B π • y := by
  induction y using TensorProduct.induction_on with
  | zero => simp only [map_zero, smul_zero]
  | add y z hy hz => simp only [map_add, smul_add, hy, hz]
  | tmul c v =>
    rw [inclBaseChange, LinearMap.baseChange_tmul, LinearMap.baseChange_tmul, algebraMap_smul,
      TensorProduct.smul_tmul', TensorProduct.smul_tmul]
    congr 1
    apply Subtype.ext
    rw [coe_smulInto_apply, Submodule.coe_inclusion, Submodule.coe_smul, algebraMap_smul]

theorem incl_smul_apply (hle : M'.1 ≤ M.1) (hπM : ∀ v ∈ M.1, algebraMap 𝒪 K π • v ∈ M'.1)
    (y : latticeBaseChange 𝒪 K B M) :
    (inclBaseChange B hle) (((smulInto π hπM).baseChange B) y) = algebraMap 𝒪 B π • y := by
  induction y using TensorProduct.induction_on with
  | zero => simp only [map_zero, smul_zero]
  | add y z hy hz => simp only [map_add, smul_add, hy, hz]
  | tmul c v =>
    rw [inclBaseChange, LinearMap.baseChange_tmul, LinearMap.baseChange_tmul, algebraMap_smul,
      TensorProduct.smul_tmul', TensorProduct.smul_tmul]
    congr 1
    apply Subtype.ext
    rw [Submodule.coe_inclusion, coe_smulInto_apply, Submodule.coe_smul, algebraMap_smul]

theorem Pi1_Pi0 (hπ : Irreducible π) (hle : M'.1 ≤ M.1) (hπM : ∀ v ∈ M.1, algebraMap 𝒪 K π • v ∈ M'.1)
    (t : T0 d M') : Pi1 d hπ hπM (Pi0 d hle t) = algebraMap 𝒪 B π • t := by
  obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective _ t
  show ((d.line M).mapQ _ _ _) (((d.line M').mapQ _ _ _) (Submodule.Quotient.mk y)) = _
  rw [Submodule.mapQ_apply, Submodule.mapQ_apply, smul_incl_apply hle hπM, Submodule.Quotient.mk_smul]
  rfl

theorem Pi0_Pi1 (hπ : Irreducible π) (hle : M'.1 ≤ M.1) (hπM : ∀ v ∈ M.1, algebraMap 𝒪 K π • v ∈ M'.1)
    (t : T1 d M) : Pi0 d hle (Pi1 d hπ hπM t) = algebraMap 𝒪 B π • t := by
  obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective _ t
  show ((d.line M').mapQ _ _ _) (((d.line M).mapQ _ _ _) (Submodule.Quotient.mk y)) = _
  rw [Submodule.mapQ_apply, Submodule.mapQ_apply, incl_smul_apply hle hπM, Submodule.Quotient.mk_smul]
  rfl

theorem Pi1_comp_Pi0 (hπ : Irreducible π) (hle : M'.1 ≤ M.1) (hπM : ∀ v ∈ M.1, algebraMap 𝒪 K π • v ∈ M'.1) :
    Pi1 d hπ hπM ∘ₗ Pi0 d hle = algebraMap 𝒪 B π • LinearMap.id :=
  LinearMap.ext fun t => by simpa using Pi1_Pi0 d hπ hle hπM t

def S0 (hle : M'.1 ≤ M.1) : Set (PrimeSpectrum B) :=
  {x | LinearMap.range (Pi0 d hle) ≤ x.asIdeal • (⊤ : Submodule B (T1 d M))}

def S1 (hπ : Irreducible π) (hπM : ∀ v ∈ M.1, algebraMap 𝒪 K π • v ∈ M'.1) : Set (PrimeSpectrum B) :=
  {x | LinearMap.range (Pi1 d hπ hπM) ≤ x.asIdeal • (⊤ : Submodule B (T0 d M'))}

theorem isClosed_S0 (hle : M'.1 ≤ M.1) : IsClosed (S0 d (M := M) hle) :=
  Module.isClosed_setOf_range_le_smul_top (Pi0 d hle)

theorem isClosed_S1 (hπ : Irreducible π) (hπM : ∀ v ∈ M.1, algebraMap 𝒪 K π • v ∈ M'.1) :
    IsClosed (S1 d hπ hπM) :=
  Module.isClosed_setOf_range_le_smul_top (Pi1 d hπ hπM)

theorem mem_S0_or_mem_S1 (hπ : Irreducible π) (hle : M'.1 ≤ M.1) (hπM : ∀ v ∈ M.1, algebraMap 𝒪 K π • v ∈ M'.1)
    (hB : IsNilpotent (algebraMap 𝒪 B π)) (x : PrimeSpectrum B) :
    x ∈ S0 d (M := M) hle ∨ x ∈ S1 d hπ hπM := by
  have hπmem : algebraMap 𝒪 B π ∈ x.asIdeal := by
    obtain ⟨n, hn⟩ := hB
    exact x.isPrime.mem_of_pow_mem n (hn ▸ x.asIdeal.zero_mem)
  exact Module.Invertible.range_le_smul_top_or_of_comp_eq_smul (Pi0 d hle) (Pi1 d hπ hπM) _
    (Pi1_comp_Pi0 d hπ hle hπM) x hπmem

end Chart

section Local

variable [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] [IsFractionRing 𝒪 K] {π : 𝒪}
variable {M' M : FullLattice 𝒪 K} (d : DeligneDatum (K := K) π B)

noncomputable def Pi0inv (hle : M'.1 ≤ M.1) (x : PrimeSpectrum B) (hx : x ∉ S0 d (M := M) hle) :
    stalk B x (T1 d M) ≃ₗ[locRing B x] stalk B x (T0 d M') :=
  (LinearEquiv.ofBijective (LocalizedModule.map x.asIdeal.primeCompl (Pi0 d hle))
    (Module.Invertible.bijective_localizedModule_map_of_not_range_le (Pi0 d hle) x hx)).symm

theorem map_Pi0_Pi0inv (hle : M'.1 ≤ M.1) (x : PrimeSpectrum B) (hx : x ∉ S0 d (M := M) hle) (t : stalk B x (T1 d M)) :
    LocalizedModule.map x.asIdeal.primeCompl (Pi0 d hle) (Pi0inv d hle x hx t) = t :=
  (LinearEquiv.ofBijective (LocalizedModule.map x.asIdeal.primeCompl (Pi0 d hle))
    (Module.Invertible.bijective_localizedModule_map_of_not_range_le (Pi0 d hle) x hx)).apply_symm_apply t

theorem Pi0inv_map_Pi0 (hle : M'.1 ≤ M.1) (x : PrimeSpectrum B) (hx : x ∉ S0 d (M := M) hle) (t : stalk B x (T0 d M')) :
    Pi0inv d hle x hx (LocalizedModule.map x.asIdeal.primeCompl (Pi0 d hle) t) = t :=
  (LinearEquiv.ofBijective (LocalizedModule.map x.asIdeal.primeCompl (Pi0 d hle))
    (Module.Invertible.bijective_localizedModule_map_of_not_range_le (Pi0 d hle) x hx)).symm_apply_apply t

noncomputable def Pi1inv (hπ : Irreducible π) (hπM : ∀ v ∈ M.1, algebraMap 𝒪 K π • v ∈ M'.1) (x : PrimeSpectrum B)
    (hx : x ∉ S1 d hπ hπM) : stalk B x (T0 d M') ≃ₗ[locRing B x] stalk B x (T1 d M) :=
  (LinearEquiv.ofBijective (LocalizedModule.map x.asIdeal.primeCompl (Pi1 d hπ hπM))
    (Module.Invertible.bijective_localizedModule_map_of_not_range_le (Pi1 d hπ hπM) x hx)).symm

theorem map_Pi1_Pi1inv (hπ : Irreducible π) (hπM : ∀ v ∈ M.1, algebraMap 𝒪 K π • v ∈ M'.1) (x : PrimeSpectrum B)
    (hx : x ∉ S1 d hπ hπM) (t : stalk B x (T0 d M')) :
    LocalizedModule.map x.asIdeal.primeCompl (Pi1 d hπ hπM) (Pi1inv d hπ hπM x hx t) = t :=
  (LinearEquiv.ofBijective (LocalizedModule.map x.asIdeal.primeCompl (Pi1 d hπ hπM))
    (Module.Invertible.bijective_localizedModule_map_of_not_range_le (Pi1 d hπ hπM) x hx)).apply_symm_apply t

theorem Pi1inv_map_Pi1 (hπ : Irreducible π) (hπM : ∀ v ∈ M.1, algebraMap 𝒪 K π • v ∈ M'.1) (x : PrimeSpectrum B)
    (hx : x ∉ S1 d hπ hπM) (t : stalk B x (T1 d M)) :
    Pi1inv d hπ hπM x hx (LocalizedModule.map x.asIdeal.primeCompl (Pi1 d hπ hπM) t) = t :=
  (LinearEquiv.ofBijective (LocalizedModule.map x.asIdeal.primeCompl (Pi1 d hπ hπM))
    (Module.Invertible.bijective_localizedModule_map_of_not_range_le (Pi1 d hπ hπM) x hx)).symm_apply_apply t

noncomputable abbrev Mpi (hπ : Irreducible π) (M' : FullLattice 𝒪 K) : FullLattice 𝒪 K :=
  FullLattice.act (scalarGL (piUnit (K := K) hπ)⁻¹) M'

theorem smul_mem_of_mem_Mpi (hπ : Irreducible π) (M' : FullLattice 𝒪 K) :
    ∀ v ∈ (Mpi (K := K) hπ M').1, algebraMap 𝒪 K π • v ∈ M'.1 := by
  intro v hv
  obtain ⟨w, hw, rfl⟩ := mem_latticeMap_scalarGL.mp hv
  have : algebraMap 𝒪 K π • (((piUnit (K := K) hπ)⁻¹ : Kˣ) : K) • w = w := by
    rw [smul_smul, Units.val_inv_eq_inv_val, show algebraMap 𝒪 K π = ((piUnit (K := K) hπ : Kˣ) : K) from rfl,
      mul_inv_cancel₀ (piUnit (K := K) hπ).ne_zero, one_smul]
  rw [this]; exact hw

noncomputable def sPi (hπ : Irreducible π) (M' : FullLattice 𝒪 K) (x : PrimeSpectrum B) :
    latticeBaseChange 𝒪 K (locRing B x) (Mpi (K := K) hπ M') →ₗ[locRing B x] latticeBaseChange 𝒪 K (locRing B x) M' :=
  (smulInto π (smul_mem_of_mem_Mpi (K := K) hπ M')).baseChange (locRing B x)

theorem sPi_surjective (hπ : Irreducible π) (M' : FullLattice 𝒪 K) (x : PrimeSpectrum B) :
    Function.Surjective (sPi (B := B) hπ M' x) := by
  rw [sPi, LinearMap.baseChange_eq_ltensor]
  refine LinearMap.lTensor_surjective _ fun w => ?_
  refine ⟨⟨(((piUnit (K := K) hπ)⁻¹ : Kˣ) : K) • (w : Fin 2 → K), ?_⟩, ?_⟩
  · exact mem_latticeMap_scalarGL.mpr ⟨w, w.2, rfl⟩
  · apply Subtype.ext
    rw [coe_smulInto_apply, smul_smul, Units.val_inv_eq_inv_val,
      show algebraMap 𝒪 K π = ((piUnit (K := K) hπ : Kˣ) : K) from rfl, mul_inv_cancel₀ (piUnit (K := K) hπ).ne_zero,
      one_smul]

open Classical in

noncomputable def loc₀ (hle : M'.1 ≤ M.1) (x : PrimeSpectrum B) :
    Σ L : FullLattice 𝒪 K, (latticeBaseChange 𝒪 K (locRing B x) L →ₗ[locRing B x] stalk B x (T0 d M')) :=
  if hx : x ∈ S0 d (M := M) hle then ⟨M', stalkQuot x M' (d.line M')⟩
  else ⟨M, (Pi0inv d hle x hx).toLinearMap ∘ₗ stalkQuot x M (d.line M)⟩

open Classical in

noncomputable def loc₁ (hπ : Irreducible π) (hπM : ∀ v ∈ M.1, algebraMap 𝒪 K π • v ∈ M'.1) (x : PrimeSpectrum B) :
    Σ L : FullLattice 𝒪 K, (latticeBaseChange 𝒪 K (locRing B x) L →ₗ[locRing B x] stalk B x (T1 d M)) :=
  if hx : x ∈ S1 d hπ hπM then ⟨M, stalkQuot x M (d.line M)⟩
  else ⟨Mpi (K := K) hπ M', (Pi1inv d hπ hπM x hx).toLinearMap ∘ₗ stalkQuot x M' (d.line M') ∘ₗ sPi hπ M' x⟩

theorem loc₀_eq_of_mem (hle : M'.1 ≤ M.1) {x : PrimeSpectrum B} (hx : x ∈ S0 d (M := M) hle) :
    loc₀ d hle x = ⟨M', stalkQuot x M' (d.line M')⟩ := by
  simp only [loc₀, dif_pos hx]

theorem loc₀_eq_of_not_mem (hle : M'.1 ≤ M.1) {x : PrimeSpectrum B} (hx : x ∉ S0 d (M := M) hle) :
    loc₀ d hle x = ⟨M, (Pi0inv d hle x hx).toLinearMap ∘ₗ stalkQuot x M (d.line M)⟩ := by
  simp only [loc₀, dif_neg hx]

theorem loc₁_eq_of_mem (hπ : Irreducible π) (hπM : ∀ v ∈ M.1, algebraMap 𝒪 K π • v ∈ M'.1) {x : PrimeSpectrum B}
    (hx : x ∈ S1 d hπ hπM) : loc₁ d hπ hπM x = ⟨M, stalkQuot x M (d.line M)⟩ := by
  simp only [loc₁, dif_pos hx]

theorem loc₁_eq_of_not_mem (hπ : Irreducible π) (hπM : ∀ v ∈ M.1, algebraMap 𝒪 K π • v ∈ M'.1) {x : PrimeSpectrum B}
    (hx : x ∉ S1 d hπ hπM) :
    loc₁ d hπ hπM x = ⟨Mpi (K := K) hπ M',
      (Pi1inv d hπ hπM x hx).toLinearMap ∘ₗ stalkQuot x M' (d.line M') ∘ₗ sPi hπ M' x⟩ := by
  simp only [loc₁, dif_neg hx]

theorem loc₀_fst_of_mem (hle : M'.1 ≤ M.1) {x : PrimeSpectrum B} (hx : x ∈ S0 d (M := M) hle) :
    (loc₀ d hle x).1 = M' := by rw [loc₀_eq_of_mem d hle hx]
theorem loc₀_fst_of_not_mem (hle : M'.1 ≤ M.1) {x : PrimeSpectrum B} (hx : x ∉ S0 d (M := M) hle) :
    (loc₀ d hle x).1 = M := by rw [loc₀_eq_of_not_mem d hle hx]
theorem loc₁_fst_of_mem (hπ : Irreducible π) (hπM : ∀ v ∈ M.1, algebraMap 𝒪 K π • v ∈ M'.1) {x : PrimeSpectrum B}
    (hx : x ∈ S1 d hπ hπM) : (loc₁ d hπ hπM x).1 = M := by rw [loc₁_eq_of_mem d hπ hπM hx]
theorem loc₁_fst_of_not_mem (hπ : Irreducible π) (hπM : ∀ v ∈ M.1, algebraMap 𝒪 K π • v ∈ M'.1) {x : PrimeSpectrum B}
    (hx : x ∉ S1 d hπ hπM) : (loc₁ d hπ hπM x).1 = FullLattice.act (scalarGL (piUnit (K := K) hπ)⁻¹) M' := by
  rw [loc₁_eq_of_not_mem d hπ hπM hx]

theorem loc₀_surjective (hle : M'.1 ≤ M.1) (x : PrimeSpectrum B) : Function.Surjective (loc₀ d hle x).2 := by
  by_cases hx : x ∈ S0 d (M := M) hle
  · rw [loc₀_eq_of_mem d hle hx]; exact stalkQuot_surjective x M' (d.line M')
  · rw [loc₀_eq_of_not_mem d hle hx]
    exact (Pi0inv d hle x hx).surjective.comp (stalkQuot_surjective x M (d.line M))

theorem loc₁_surjective (hπ : Irreducible π) (hπM : ∀ v ∈ M.1, algebraMap 𝒪 K π • v ∈ M'.1) (x : PrimeSpectrum B) :
    Function.Surjective (loc₁ d hπ hπM x).2 := by
  by_cases hx : x ∈ S1 d hπ hπM
  · rw [loc₁_eq_of_mem d hπ hπM hx]; exact stalkQuot_surjective x M (d.line M)
  · rw [loc₁_eq_of_not_mem d hπ hπM hx]
    exact (Pi1inv d hπ hπM x hx).surjective.comp
      ((stalkQuot_surjective x M' (d.line M')).comp (sPi_surjective hπ M' x))

theorem stalkQuot_naturality (x : PrimeSpectrum B) {L L' : FullLattice 𝒪 K}
    (N : Submodule B (latticeBaseChange 𝒪 K B L)) (N' : Submodule B (latticeBaseChange 𝒪 K B L'))
    (φ : ↥L.1 → ↥L'.1)
    (g : latticeBaseChange 𝒪 K B L →ₗ[B] latticeBaseChange 𝒪 K B L') (hg : ∀ v, g ((1 : B) ⊗ₜ[𝒪] v) = (1 : B) ⊗ₜ[𝒪] φ v)
    (hN : N ≤ N'.comap g)
    (gx : latticeBaseChange 𝒪 K (locRing B x) L →ₗ[locRing B x] latticeBaseChange 𝒪 K (locRing B x) L')
    (hgx : ∀ v, gx ((1 : locRing B x) ⊗ₜ[𝒪] v) = (1 : locRing B x) ⊗ₜ[𝒪] φ v)
    (w : latticeBaseChange 𝒪 K (locRing B x) L) :
    stalkQuot x L' N' (gx w) = LocalizedModule.map x.asIdeal.primeCompl (Submodule.mapQ N N' g hN) (stalkQuot x L N w) := by
  induction w using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add w₁ w₂ h₁ h₂ => simp only [map_add, h₁, h₂]
  | tmul b v =>
    have hb : b ⊗ₜ[𝒪] v = b • ((1 : locRing B x) ⊗ₜ[𝒪] v) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [hb, map_smul, map_smul, map_smul, hgx, stalkQuot_one_tmul, stalkQuot_one_tmul,
      LocalizedModule.mkLinearMap_apply, LocalizedModule.mkLinearMap_apply, LinearMap.map_smul,
      LocalizedModule.map_mk, Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.mapQ_apply, hg]

theorem stalkQuot_incl (hle : M'.1 ≤ M.1) (x : PrimeSpectrum B) (w : latticeBaseChange 𝒪 K (locRing B x) M') :
    stalkQuot x M (d.line M) (inclBaseChange (locRing B x) hle w) =
      LocalizedModule.map x.asIdeal.primeCompl (Pi0 d hle) (stalkQuot x M' (d.line M') w) := by
  refine stalkQuot_naturality x (d.line M') (d.line M) (Submodule.inclusion hle) (inclBaseChange B hle)
    (fun v => ?_) _ (inclBaseChange (locRing B x) hle) (fun v => ?_) w
  · rw [inclBaseChange, LinearMap.baseChange_tmul]
  · rw [inclBaseChange, LinearMap.baseChange_tmul]

theorem stalkQuot_smulInto (hπ : Irreducible π) (hπM : ∀ v ∈ M.1, algebraMap 𝒪 K π • v ∈ M'.1) (x : PrimeSpectrum B)
    (w : latticeBaseChange 𝒪 K (locRing B x) M) :
    stalkQuot x M' (d.line M') ((smulInto π hπM).baseChange (locRing B x) w) =
      LocalizedModule.map x.asIdeal.primeCompl (Pi1 d hπ hπM) (stalkQuot x M (d.line M) w) := by
  refine stalkQuot_naturality x (d.line M) (d.line M') (smulInto π hπM) ((smulInto π hπM).baseChange B)
    (fun v => ?_) _ ((smulInto π hπM).baseChange (locRing B x)) (fun v => ?_) w
  · rw [LinearMap.baseChange_tmul]
  · rw [LinearMap.baseChange_tmul]

theorem ker_loc₀ (hle : M'.1 ≤ M.1) (x : PrimeSpectrum B) :
    LinearMap.ker (loc₀ d hle x).2 = (d.map π (toLocRing B x)).line (loc₀ d hle x).1 := by
  by_cases hx : x ∈ S0 d (M := M) hle
  · rw [loc₀_eq_of_mem d hle hx]; exact ker_stalkQuot x M' (d.line M')
  · rw [loc₀_eq_of_not_mem d hle hx]
    show LinearMap.ker ((Pi0inv d hle x hx).toLinearMap ∘ₗ stalkQuot x M (d.line M)) = _
    rw [LinearMap.ker_comp, LinearEquiv.ker, Submodule.comap_bot]
    exact ker_stalkQuot x M (d.line M)

noncomputable def smulEquiv (hπ : Irreducible π) (M' : FullLattice 𝒪 K) : ↥(Mpi (K := K) hπ M').1 ≃ₗ[𝒪] ↥M'.1 :=
  LinearEquiv.ofBijective (smulInto π (smul_mem_of_mem_Mpi (K := K) hπ M'))
    ⟨by
      intro v w h
      apply Subtype.ext
      have := congrArg Subtype.val h
      rw [coe_smulInto_apply, coe_smulInto_apply] at this
      exact smul_right_injective _ (hπK_of_irreducible (K := K) hπ) this,
     by
      intro w
      refine ⟨⟨(((piUnit (K := K) hπ)⁻¹ : Kˣ) : K) • (w : Fin 2 → K), mem_latticeMap_scalarGL.mpr ⟨w, w.2, rfl⟩⟩, ?_⟩
      apply Subtype.ext
      rw [coe_smulInto_apply, smul_smul, Units.val_inv_eq_inv_val,
        show algebraMap 𝒪 K π = ((piUnit (K := K) hπ : Kˣ) : K) from rfl, mul_inv_cancel₀ (piUnit (K := K) hπ).ne_zero,
        one_smul]⟩

theorem sPi_eq (hπ : Irreducible π) (M' : FullLattice 𝒪 K) (x : PrimeSpectrum B) :
    sPi (B := B) hπ M' x = ((smulEquiv (K := K) hπ M').baseChange 𝒪 (locRing B x) _ _).toLinearMap := by
  refine TensorProduct.AlgebraTensorModule.ext fun b v => ?_
  rw [sPi, LinearMap.baseChange_tmul, LinearEquiv.coe_coe, LinearEquiv.baseChange_tmul]
  rfl

theorem ker_sPi (hπ : Irreducible π) (M' : FullLattice 𝒪 K) (x : PrimeSpectrum B) :
    LinearMap.ker (sPi (B := B) hπ M' x) = ⊥ := by
  rw [sPi_eq, LinearEquiv.ker]

theorem map_smulInto_line_Mpi (hπ : Irreducible π) (M' : FullLattice 𝒪 K) :
    (d.line (Mpi (K := K) hπ M')).map ((smulInto π (smul_mem_of_mem_Mpi (K := K) hπ M')).baseChange B) = d.line M' := by
  have hfac := smulInto_baseChange_eq (M := Mpi (K := K) hπ M') (M' := M') (B := B) hπ (smul_mem_of_mem_Mpi (K := K) hπ M')
  have hle1 : (FullLattice.act (scalarGL (piUnit (K := K) hπ)) (Mpi (K := K) hπ M')).1 ≤ M'.1 :=
    act_piUnit_le hπ (smul_mem_of_mem_Mpi (K := K) hπ M')
  have hle2 : M'.1 ≤ (FullLattice.act (scalarGL (piUnit (K := K) hπ)) (Mpi (K := K) hπ M')).1 := by
    intro v hv
    refine mem_latticeMap_scalarGL.mpr ⟨(((piUnit (K := K) hπ)⁻¹ : Kˣ) : K) • v,
      mem_latticeMap_scalarGL.mpr ⟨v, hv, rfl⟩, ?_⟩
    rw [smul_smul, Units.val_inv_eq_inv_val, mul_inv_cancel₀ (piUnit (K := K) hπ).ne_zero, one_smul]
  apply le_antisymm
  · rw [hfac, Submodule.map_comp, ← d.homothety (piUnit (K := K) hπ) (Mpi (K := K) hπ M')]
    exact d.mono hle1
  ·
    have hround : (inclBaseChange B hle1) ∘ₗ (inclBaseChange B hle2) = LinearMap.id := by
      refine TensorProduct.AlgebraTensorModule.ext fun b v => ?_
      rw [LinearMap.comp_apply, inclBaseChange, inclBaseChange, LinearMap.baseChange_tmul, LinearMap.baseChange_tmul,
        LinearMap.id_apply]
      rfl
    calc d.line M' = ((d.line M').map (inclBaseChange B hle2)).map (inclBaseChange B hle1) := by
          rw [← Submodule.map_comp, hround, Submodule.map_id]
      _ ≤ (d.line (FullLattice.act (scalarGL (piUnit (K := K) hπ)) (Mpi (K := K) hπ M'))).map (inclBaseChange B hle1) :=
          Submodule.map_mono (d.mono hle2)
      _ = _ := by rw [d.homothety (piUnit (K := K) hπ) (Mpi (K := K) hπ M'), ← Submodule.map_comp, ← hfac]

theorem lineBaseChange_map_baseChange {B' : Type} [CommRing B'] [Algebra 𝒪 B'] (f : B →ₐ[𝒪] B')
    {L L' : FullLattice 𝒪 K} (ψ : ↥L.1 →ₗ[𝒪] ↥L'.1) (N : Submodule B (latticeBaseChange 𝒪 K B L)) :
    lineBaseChange f L' (N.map (ψ.baseChange B)) = (lineBaseChange f L N).map (ψ.baseChange B') := by
  rw [lineBaseChange, lineBaseChange, Submodule.map_span, Submodule.map_coe, ← Set.image_comp, ← Set.image_comp]
  have key : ∀ n : latticeBaseChange 𝒪 K B L,
      (LinearMap.rTensor (↥L'.1) f.toLinearMap) ((ψ.baseChange B) n) =
        (ψ.baseChange B') ((LinearMap.rTensor (↥L.1) f.toLinearMap) n) := by
    intro n
    induction n using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | add n₁ n₂ h₁ h₂ => simp only [map_add, h₁, h₂]
    | tmul b v => rw [LinearMap.baseChange_tmul, LinearMap.rTensor_tmul, LinearMap.rTensor_tmul, LinearMap.baseChange_tmul]
  congr 1
  exact Set.image_congr fun n _ => by simp only [Function.comp_apply, key]

theorem ker_loc₁ (hπ : Irreducible π) (hπM : ∀ v ∈ M.1, algebraMap 𝒪 K π • v ∈ M'.1) (x : PrimeSpectrum B) :
    LinearMap.ker (loc₁ d hπ hπM x).2 = (d.map π (toLocRing B x)).line (loc₁ d hπ hπM x).1 := by
  by_cases hx : x ∈ S1 d hπ hπM
  · rw [loc₁_eq_of_mem d hπ hπM hx]; exact ker_stalkQuot x M (d.line M)
  · rw [loc₁_eq_of_not_mem d hπ hπM hx]
    show LinearMap.ker ((Pi1inv d hπ hπM x hx).toLinearMap ∘ₗ stalkQuot x M' (d.line M') ∘ₗ sPi hπ M' x) =
      lineBaseChange (toLocRing B x) (Mpi (K := K) hπ M') (d.line (Mpi (K := K) hπ M'))
    rw [LinearMap.ker_comp, LinearEquiv.ker, Submodule.comap_bot, LinearMap.ker_comp, ker_stalkQuot,
      ← map_smulInto_line_Mpi d hπ M', lineBaseChange_map_baseChange, ← sPi, Submodule.comap_map_eq, ker_sPi, sup_bot_eq]

theorem le_Mpi (hπ : Irreducible π) (hle : M'.1 ≤ M.1) (hπM : ∀ v ∈ M.1, algebraMap 𝒪 K π • v ∈ M'.1) :
    M.1 ≤ (Mpi (K := K) hπ M').1 := by
  intro v hv
  refine mem_latticeMap_scalarGL.mpr ⟨algebraMap 𝒪 K π • v, hπM v hv, ?_⟩
  rw [smul_smul, Units.val_inv_eq_inv_val, show algebraMap 𝒪 K π = ((piUnit (K := K) hπ : Kˣ) : K) from rfl,
    inv_mul_cancel₀ (piUnit (K := K) hπ).ne_zero, one_smul]

theorem loc_le (hπ : Irreducible π) (hle : M'.1 ≤ M.1) (hπM : ∀ v ∈ M.1, algebraMap 𝒪 K π • v ∈ M'.1)
    (x : PrimeSpectrum B) : (loc₀ d hle x).1.1 ≤ (loc₁ d hπ hπM x).1.1 := by
  by_cases h0 : x ∈ S0 d (M := M) hle <;> by_cases h1 : x ∈ S1 d hπ hπM
  · rw [loc₀_fst_of_mem d hle h0, loc₁_fst_of_mem d hπ hπM h1]; exact hle
  · rw [loc₀_fst_of_mem d hle h0, loc₁_fst_of_not_mem d hπ hπM h1]; exact hle.trans (le_Mpi hπ hle hπM)
  · rw [loc₀_fst_of_not_mem d hle h0, loc₁_fst_of_mem d hπ hπM h1]
  · rw [loc₀_fst_of_not_mem d hle h0, loc₁_fst_of_not_mem d hπ hπM h1]; exact le_Mpi hπ hle hπM

theorem loc_smul_le (hπ : Irreducible π) (hle : M'.1 ≤ M.1) (hπM : ∀ v ∈ M.1, algebraMap 𝒪 K π • v ∈ M'.1)
    (x : PrimeSpectrum B) : ∀ v ∈ (loc₁ d hπ hπM x).1.1, algebraMap 𝒪 K π • v ∈ (loc₀ d hle x).1.1 := by
  by_cases h0 : x ∈ S0 d (M := M) hle <;> by_cases h1 : x ∈ S1 d hπ hπM
  · rw [loc₀_fst_of_mem d hle h0, loc₁_fst_of_mem d hπ hπM h1]; exact hπM
  · rw [loc₀_fst_of_mem d hle h0, loc₁_fst_of_not_mem d hπ hπM h1]; exact smul_mem_of_mem_Mpi hπ M'
  · rw [loc₀_fst_of_not_mem d hle h0, loc₁_fst_of_mem d hπ hπM h1]; exact fun v hv => hle (hπM v hv)
  · rw [loc₀_fst_of_not_mem d hle h0, loc₁_fst_of_not_mem d hπ hπM h1]
    exact fun v hv => hle (smul_mem_of_mem_Mpi hπ M' v hv)

theorem sPi_incl (hπ : Irreducible π) (x : PrimeSpectrum B) (h : M'.1 ≤ (Mpi (K := K) hπ M').1)
    (w : latticeBaseChange 𝒪 K (locRing B x) M') :
    sPi hπ M' x (inclBaseChange (locRing B x) h w) = algebraMap 𝒪 B π • w := by
  induction w using TensorProduct.induction_on with
  | zero => simp only [map_zero, smul_zero]
  | add y z hy hz => simp only [map_add, smul_add, hy, hz]
  | tmul c v =>
    rw [inclBaseChange, LinearMap.baseChange_tmul, sPi, LinearMap.baseChange_tmul, algebraMap_smul,
      TensorProduct.smul_tmul', TensorProduct.smul_tmul]
    congr 1
    apply Subtype.ext
    rw [coe_smulInto_apply, Submodule.coe_inclusion, Submodule.coe_smul, algebraMap_smul]

theorem smulInto_self (x : PrimeSpectrum B) (h : ∀ v ∈ M.1, algebraMap 𝒪 K π • v ∈ M.1)
    (w : latticeBaseChange 𝒪 K (locRing B x) M) :
    (smulInto π h).baseChange (locRing B x) w = algebraMap 𝒪 B π • w := by
  induction w using TensorProduct.induction_on with
  | zero => simp only [map_zero, smul_zero]
  | add y z hy hz => simp only [map_add, smul_add, hy, hz]
  | tmul c v =>
    rw [LinearMap.baseChange_tmul, algebraMap_smul, TensorProduct.smul_tmul', TensorProduct.smul_tmul]
    congr 1
    apply Subtype.ext
    rw [coe_smulInto_apply, Submodule.coe_smul, algebraMap_smul]

theorem sPi_incl' (hπ : Irreducible π) (hπM : ∀ v ∈ M.1, algebraMap 𝒪 K π • v ∈ M'.1) (x : PrimeSpectrum B)
    (h : M.1 ≤ (Mpi (K := K) hπ M').1) (w : latticeBaseChange 𝒪 K (locRing B x) M) :
    sPi hπ M' x (inclBaseChange (locRing B x) h w) = (smulInto π hπM).baseChange (locRing B x) w := by
  induction w using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add y z hy hz => simp only [map_add, hy, hz]
  | tmul c v =>
    rw [inclBaseChange, LinearMap.baseChange_tmul, sPi, LinearMap.baseChange_tmul, LinearMap.baseChange_tmul]
    congr 1

theorem incl_sPi (hπ : Irreducible π) (hle : M'.1 ≤ M.1) (x : PrimeSpectrum B)
    (h : ∀ v ∈ (Mpi (K := K) hπ M').1, algebraMap 𝒪 K π • v ∈ M.1) (w : latticeBaseChange 𝒪 K (locRing B x) (Mpi (K := K) hπ M')) :
    (smulInto π h).baseChange (locRing B x) w = inclBaseChange (locRing B x) hle (sPi hπ M' x w) := by
  induction w using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add y z hy hz => simp only [map_add, hy, hz]
  | tmul c v =>
    rw [inclBaseChange, sPi, LinearMap.baseChange_tmul, LinearMap.baseChange_tmul, LinearMap.baseChange_tmul]
    congr 1

theorem incl_self (x : PrimeSpectrum B) (h : M.1 ≤ M.1) (w : latticeBaseChange 𝒪 K (locRing B x) M) :
    inclBaseChange (locRing B x) h w = w := by
  induction w using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add y z hy hz => simp only [map_add, hy, hz]
  | tmul c v => rw [inclBaseChange, LinearMap.baseChange_tmul]; rfl

theorem map_Pi1_map_Pi0 (hπ : Irreducible π) (hle : M'.1 ≤ M.1) (hπM : ∀ v ∈ M.1, algebraMap 𝒪 K π • v ∈ M'.1)
    (x : PrimeSpectrum B) (t : stalk B x (T0 d M')) :
    LocalizedModule.map x.asIdeal.primeCompl (Pi1 d hπ hπM) (LocalizedModule.map x.asIdeal.primeCompl (Pi0 d hle) t) =
      algebraMap 𝒪 B π • t := by
  induction t using LocalizedModule.induction_on with
  | h m s => rw [LocalizedModule.map_mk, LocalizedModule.map_mk, Pi1_Pi0 d hπ hle hπM, LocalizedModule.smul'_mk]

theorem map_Pi0_map_Pi1 (hπ : Irreducible π) (hle : M'.1 ≤ M.1) (hπM : ∀ v ∈ M.1, algebraMap 𝒪 K π • v ∈ M'.1)
    (x : PrimeSpectrum B) (t : stalk B x (T1 d M)) :
    LocalizedModule.map x.asIdeal.primeCompl (Pi0 d hle) (LocalizedModule.map x.asIdeal.primeCompl (Pi1 d hπ hπM) t) =
      algebraMap 𝒪 B π • t := by
  induction t using LocalizedModule.induction_on with
  | h m s => rw [LocalizedModule.map_mk, LocalizedModule.map_mk, Pi0_Pi1 d hπ hle hπM, LocalizedModule.smul'_mk]

theorem u₁_incl_loc (hπ : Irreducible π) (hle : M'.1 ≤ M.1) (hπM : ∀ v ∈ M.1, algebraMap 𝒪 K π • v ∈ M'.1)
    (x : PrimeSpectrum B) (hl : (loc₀ d hle x).1.1 ≤ (loc₁ d hπ hπM x).1.1)
    (w : latticeBaseChange 𝒪 K (locRing B x) (loc₀ d hle x).1) :
    (loc₁ d hπ hπM x).2 (inclBaseChange (locRing B x) (M' := (loc₀ d hle x).1) (M := (loc₁ d hπ hπM x).1) hl w) =
      LocalizedModule.map x.asIdeal.primeCompl (Pi0 d hle) ((loc₀ d hle x).2 w) := by
  revert w
  by_cases h0 : x ∈ S0 d (M := M) hle <;> by_cases h1 : x ∈ S1 d hπ hπM
  · have e0 := loc₀_eq_of_mem d hle h0; have e1 := loc₁_eq_of_mem d hπ hπM h1
    generalize loc₀ d hle x = p₀ at e0 hl ⊢; generalize loc₁ d hπ hπM x = p₁ at e1 hl ⊢
    subst e0 e1
    dsimp only at hl
    intro w; exact stalkQuot_incl d hle x w
  · have e0 := loc₀_eq_of_mem d hle h0; have e1 := loc₁_eq_of_not_mem d hπ hπM h1
    generalize loc₀ d hle x = p₀ at e0 hl ⊢; generalize loc₁ d hπ hπM x = p₁ at e1 hl ⊢
    subst e0 e1
    dsimp only at hl
    intro w
    show (Pi1inv d hπ hπM x h1) (stalkQuot x M' (d.line M') (sPi hπ M' x (inclBaseChange (locRing B x) hl w))) = _
    rw [sPi_incl, ← algebraMap_smul (locRing B x), map_smul, algebraMap_smul, ← map_Pi1_map_Pi0 d hπ hle hπM x,
      Pi1inv_map_Pi1]
  · have e0 := loc₀_eq_of_not_mem d hle h0; have e1 := loc₁_eq_of_mem d hπ hπM h1
    generalize loc₀ d hle x = p₀ at e0 hl ⊢; generalize loc₁ d hπ hπM x = p₁ at e1 hl ⊢
    subst e0 e1
    dsimp only at hl
    intro w
    show stalkQuot x M (d.line M) (inclBaseChange (locRing B x) hl w) =
      LocalizedModule.map x.asIdeal.primeCompl (Pi0 d hle) ((Pi0inv d hle x h0) (stalkQuot x M (d.line M) w))
    rw [incl_self, map_Pi0_Pi0inv]
  · have e0 := loc₀_eq_of_not_mem d hle h0; have e1 := loc₁_eq_of_not_mem d hπ hπM h1
    generalize loc₀ d hle x = p₀ at e0 hl ⊢; generalize loc₁ d hπ hπM x = p₁ at e1 hl ⊢
    subst e0 e1
    dsimp only at hl
    intro w
    show (Pi1inv d hπ hπM x h1) (stalkQuot x M' (d.line M') (sPi hπ M' x (inclBaseChange (locRing B x) hl w))) =
      LocalizedModule.map x.asIdeal.primeCompl (Pi0 d hle) ((Pi0inv d hle x h0) (stalkQuot x M (d.line M) w))
    rw [sPi_incl' hπ hπM, stalkQuot_smulInto d hπ hπM, Pi1inv_map_Pi1, map_Pi0_Pi0inv]

theorem u₀_smul_loc (hπ : Irreducible π) (hle : M'.1 ≤ M.1) (hπM : ∀ v ∈ M.1, algebraMap 𝒪 K π • v ∈ M'.1)
    (x : PrimeSpectrum B) (hl : ∀ v ∈ (loc₁ d hπ hπM x).1.1, algebraMap 𝒪 K π • v ∈ (loc₀ d hle x).1.1)
    (w : latticeBaseChange 𝒪 K (locRing B x) (loc₁ d hπ hπM x).1) :
    (loc₀ d hle x).2 (((smulInto π hl).baseChange (locRing B x) :
        latticeBaseChange 𝒪 K (locRing B x) (loc₁ d hπ hπM x).1 →ₗ[locRing B x]
          latticeBaseChange 𝒪 K (locRing B x) (loc₀ d hle x).1) w) =
      LocalizedModule.map x.asIdeal.primeCompl (Pi1 d hπ hπM) ((loc₁ d hπ hπM x).2 w) := by
  revert w
  by_cases h0 : x ∈ S0 d (M := M) hle <;> by_cases h1 : x ∈ S1 d hπ hπM
  · have e0 := loc₀_eq_of_mem d hle h0; have e1 := loc₁_eq_of_mem d hπ hπM h1
    generalize loc₀ d hle x = p₀ at e0 hl ⊢; generalize loc₁ d hπ hπM x = p₁ at e1 hl ⊢
    subst e0 e1
    dsimp only at hl
    intro w; exact stalkQuot_smulInto d hπ hπM x w
  · have e0 := loc₀_eq_of_mem d hle h0; have e1 := loc₁_eq_of_not_mem d hπ hπM h1
    generalize loc₀ d hle x = p₀ at e0 hl ⊢; generalize loc₁ d hπ hπM x = p₁ at e1 hl ⊢
    subst e0 e1
    dsimp only at hl
    intro w
    show stalkQuot x M' (d.line M') ((smulInto π hl).baseChange (locRing B x) w) =
      LocalizedModule.map x.asIdeal.primeCompl (Pi1 d hπ hπM)
        ((Pi1inv d hπ hπM x h1) (stalkQuot x M' (d.line M') (sPi hπ M' x w)))
    rw [map_Pi1_Pi1inv]; rfl
  · have e0 := loc₀_eq_of_not_mem d hle h0; have e1 := loc₁_eq_of_mem d hπ hπM h1
    generalize loc₀ d hle x = p₀ at e0 hl ⊢; generalize loc₁ d hπ hπM x = p₁ at e1 hl ⊢
    subst e0 e1
    dsimp only at hl
    intro w
    show (Pi0inv d hle x h0) (stalkQuot x M (d.line M) ((smulInto π hl).baseChange (locRing B x) w)) =
      LocalizedModule.map x.asIdeal.primeCompl (Pi1 d hπ hπM) (stalkQuot x M (d.line M) w)
    rw [smulInto_self, ← algebraMap_smul (locRing B x), map_smul, algebraMap_smul, ← map_Pi0_map_Pi1 d hπ hle hπM x,
      Pi0inv_map_Pi0]
  · have e0 := loc₀_eq_of_not_mem d hle h0; have e1 := loc₁_eq_of_not_mem d hπ hπM h1
    generalize loc₀ d hle x = p₀ at e0 hl ⊢; generalize loc₁ d hπ hπM x = p₁ at e1 hl ⊢
    subst e0 e1
    dsimp only at hl
    intro w
    show (Pi0inv d hle x h0) (stalkQuot x M (d.line M) ((smulInto π hl).baseChange (locRing B x) w)) =
      LocalizedModule.map x.asIdeal.primeCompl (Pi1 d hπ hπM)
        ((Pi1inv d hπ hπM x h1) (stalkQuot x M' (d.line M') (sPi hπ M' x w)))
    have key := incl_sPi (B := B) hπ hle x hl w
    rw [key, stalkQuot_incl d hle, Pi0inv_map_Pi0, map_Pi1_Pi1inv]

theorem isOpen_setOf_mem_loc₀ (hle : M'.1 ≤ M.1) (v : Fin 2 → K) :
    IsOpen {x : PrimeSpectrum B | v ∈ (loc₀ d hle x).1.1} := by
  by_cases hv' : v ∈ M'.1
  · have : {x : PrimeSpectrum B | v ∈ (loc₀ d hle x).1.1} = Set.univ := by
      ext x; simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
      by_cases hx : x ∈ S0 d (M := M) hle
      · rw [loc₀_fst_of_mem d hle hx]; exact hv'
      · rw [loc₀_fst_of_not_mem d hle hx]; exact hle hv'
    rw [this]; exact isOpen_univ
  · by_cases hv : v ∈ M.1
    · have : {x : PrimeSpectrum B | v ∈ (loc₀ d hle x).1.1} = (S0 d (M := M) hle)ᶜ := by
        ext x; simp only [Set.mem_setOf_eq, Set.mem_compl_iff]
        by_cases hx : x ∈ S0 d (M := M) hle
        · rw [loc₀_fst_of_mem d hle hx]; exact ⟨fun h => absurd h hv', fun h => absurd hx h⟩
        · rw [loc₀_fst_of_not_mem d hle hx]; exact ⟨fun _ => hx, fun _ => hv⟩
      rw [this]; exact (isClosed_S0 d hle).isOpen_compl
    · have : {x : PrimeSpectrum B | v ∈ (loc₀ d hle x).1.1} = ∅ := by
        ext x; simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
        by_cases hx : x ∈ S0 d (M := M) hle
        · rw [loc₀_fst_of_mem d hle hx]; exact hv'
        · rw [loc₀_fst_of_not_mem d hle hx]; exact hv
      rw [this]; exact isOpen_empty

theorem isOpen_setOf_mem_loc₁ (hπ : Irreducible π) (hle : M'.1 ≤ M.1) (hπM : ∀ v ∈ M.1, algebraMap 𝒪 K π • v ∈ M'.1)
    (v : Fin 2 → K) : IsOpen {x : PrimeSpectrum B | v ∈ (loc₁ d hπ hπM x).1.1} := by
  by_cases hv : v ∈ M.1
  · have : {x : PrimeSpectrum B | v ∈ (loc₁ d hπ hπM x).1.1} = Set.univ := by
      ext x; simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
      by_cases hx : x ∈ S1 d hπ hπM
      · rw [loc₁_fst_of_mem d hπ hπM hx]; exact hv
      · rw [loc₁_fst_of_not_mem d hπ hπM hx]; exact le_Mpi hπ hle hπM hv
    rw [this]; exact isOpen_univ
  · by_cases hv' : v ∈ (Mpi (K := K) hπ M').1
    · have : {x : PrimeSpectrum B | v ∈ (loc₁ d hπ hπM x).1.1} = (S1 d hπ hπM)ᶜ := by
        ext x; simp only [Set.mem_setOf_eq, Set.mem_compl_iff]
        by_cases hx : x ∈ S1 d hπ hπM
        · rw [loc₁_fst_of_mem d hπ hπM hx]; exact ⟨fun h => absurd h hv, fun h => absurd hx h⟩
        · rw [loc₁_fst_of_not_mem d hπ hπM hx]; exact ⟨fun _ => hx, fun _ => hv'⟩
      rw [this]; exact (isClosed_S1 d hπ hπM).isOpen_compl
    · have : {x : PrimeSpectrum B | v ∈ (loc₁ d hπ hπM x).1.1} = ∅ := by
        ext x; simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
        by_cases hx : x ∈ S1 d hπ hπM
        · rw [loc₁_fst_of_mem d hπ hπM hx]; exact hv
        · rw [loc₁_fst_of_not_mem d hπ hπM hx]; exact hv'
      rw [this]; exact isOpen_empty

theorem Pi0_mkQ_tmul (hle : M'.1 ≤ M.1) (b : B) (v : Fin 2 → K) (hv : v ∈ M'.1) :
    Pi0 d hle ((d.line M').mkQ (b ⊗ₜ[𝒪] (⟨v, hv⟩ : ↥M'.1))) = (d.line M).mkQ (b ⊗ₜ[𝒪] (⟨v, hle hv⟩ : ↥M.1)) := by
  rw [Pi0, Submodule.mkQ_apply, Submodule.mapQ_apply, inclBaseChange, LinearMap.baseChange_tmul]
  rfl

theorem Pi1_mkQ_tmul (hπ : Irreducible π) (hπM : ∀ v ∈ M.1, algebraMap 𝒪 K π • v ∈ M'.1) (b : B) (v : Fin 2 → K)
    (hv : v ∈ M.1) :
    Pi1 d hπ hπM ((d.line M).mkQ (b ⊗ₜ[𝒪] (⟨v, hv⟩ : ↥M.1))) =
      (d.line M').mkQ (b ⊗ₜ[𝒪] (⟨algebraMap 𝒪 K π • v, hπM v hv⟩ : ↥M'.1)) := by
  rw [Pi1, Submodule.mkQ_apply, Submodule.mapQ_apply, LinearMap.baseChange_tmul]
  rfl

theorem val_loc₀_on (hle : M'.1 ≤ M.1) {y : PrimeSpectrum B} (hy : y ∈ S0 d (M := M) hle) (v : Fin 2 → K)
    (hv : v ∈ (loc₀ d hle y).1.1) (hv' : v ∈ M'.1) :
    (loc₀ d hle y).2 ((1 : locRing B y) ⊗ₜ[𝒪] (⟨v, hv⟩ : ↥(loc₀ d hle y).1.1)) =
      LocalizedModule.mk ((d.line M').mkQ ((1 : B) ⊗ₜ[𝒪] (⟨v, hv'⟩ : ↥M'.1))) 1 := by
  have e0 := loc₀_eq_of_mem d hle hy
  revert hv
  generalize loc₀ d hle y = p₀ at e0 ⊢
  subst e0
  intro hv
  exact (stalkQuot_one_tmul y M' (d.line M') ⟨v, hv⟩).trans (LocalizedModule.mkLinearMap_apply _ _ _)

theorem val_loc₀_off (hle : M'.1 ≤ M.1) {y : PrimeSpectrum B} (hy : y ∉ S0 d (M := M) hle) (v : Fin 2 → K)
    (hv : v ∈ (loc₀ d hle y).1.1) (hvM : v ∈ M.1) :
    (loc₀ d hle y).2 ((1 : locRing B y) ⊗ₜ[𝒪] (⟨v, hv⟩ : ↥(loc₀ d hle y).1.1)) =
      Pi0inv d hle y hy (LocalizedModule.mk ((d.line M).mkQ ((1 : B) ⊗ₜ[𝒪] (⟨v, hvM⟩ : ↥M.1))) 1) := by
  have e0 := loc₀_eq_of_not_mem d hle hy
  revert hv
  generalize loc₀ d hle y = p₀ at e0 ⊢
  subst e0
  intro hv
  show Pi0inv d hle y hy (stalkQuot y M (d.line M) ((1 : locRing B y) ⊗ₜ[𝒪] (⟨v, hv⟩ : ↥M.1))) = _
  rw [stalkQuot_one_tmul, LocalizedModule.mkLinearMap_apply]

theorem val_loc₁_on (hπ : Irreducible π) (hπM : ∀ v ∈ M.1, algebraMap 𝒪 K π • v ∈ M'.1) {y : PrimeSpectrum B}
    (hy : y ∈ S1 d hπ hπM) (v : Fin 2 → K) (hv : v ∈ (loc₁ d hπ hπM y).1.1) (hvM : v ∈ M.1) :
    (loc₁ d hπ hπM y).2 ((1 : locRing B y) ⊗ₜ[𝒪] (⟨v, hv⟩ : ↥(loc₁ d hπ hπM y).1.1)) =
      LocalizedModule.mk ((d.line M).mkQ ((1 : B) ⊗ₜ[𝒪] (⟨v, hvM⟩ : ↥M.1))) 1 := by
  have e1 := loc₁_eq_of_mem d hπ hπM hy
  revert hv
  generalize loc₁ d hπ hπM y = p₁ at e1 ⊢
  subst e1
  intro hv
  exact (stalkQuot_one_tmul y M (d.line M) ⟨v, hv⟩).trans (LocalizedModule.mkLinearMap_apply _ _ _)

theorem val_loc₁_off (hπ : Irreducible π) (hπM : ∀ v ∈ M.1, algebraMap 𝒪 K π • v ∈ M'.1) {y : PrimeSpectrum B}
    (hy : y ∉ S1 d hπ hπM) (v : Fin 2 → K) (hv : v ∈ (loc₁ d hπ hπM y).1.1)
    (hvπ : algebraMap 𝒪 K π • v ∈ M'.1) :
    (loc₁ d hπ hπM y).2 ((1 : locRing B y) ⊗ₜ[𝒪] (⟨v, hv⟩ : ↥(loc₁ d hπ hπM y).1.1)) =
      Pi1inv d hπ hπM y hy
        (LocalizedModule.mk ((d.line M').mkQ ((1 : B) ⊗ₜ[𝒪] (⟨algebraMap 𝒪 K π • v, hvπ⟩ : ↥M'.1))) 1) := by
  have e1 := loc₁_eq_of_not_mem d hπ hπM hy
  revert hv
  generalize loc₁ d hπ hπM y = p₁ at e1 ⊢
  subst e1
  intro hv
  show Pi1inv d hπ hπM y hy (stalkQuot y M' (d.line M') (sPi hπ M' y ((1 : locRing B y) ⊗ₜ[𝒪] ⟨v, hv⟩))) = _
  rw [sPi, LinearMap.baseChange_tmul, stalkQuot_one_tmul, LocalizedModule.mkLinearMap_apply]
  rfl

omit [Algebra 𝒪 K] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] [IsFractionRing 𝒪 K] in

theorem exists_basicOpen_subset_compl {S : Set (PrimeSpectrum B)} (hS : IsClosed S) {x : PrimeSpectrum B} (hx : x ∉ S) :
    ∃ g : B, g ∉ x.asIdeal ∧ ∀ y : PrimeSpectrum B, g ∉ y.asIdeal → y ∉ S := by
  obtain ⟨U, ⟨g, rfl⟩, hxg, hgS⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open (a := x) (by exact hx) hS.isOpen_compl
  exact ⟨g, hxg, fun y hy => hgS hy⟩

omit [Algebra 𝒪 K] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] [IsFractionRing 𝒪 K] in

theorem exists_section_of_bijective {P Q : Type} [AddCommGroup P] [Module B P] [AddCommGroup Q] [Module B Q]
    (F : P →ₗ[B] Q) (x : PrimeSpectrum B) (hF : Function.Bijective (LocalizedModule.map x.asIdeal.primeCompl F))
    (g : B) (hg : g ∉ x.asIdeal) (m : Q) :
    ∃ (f : B) (t : P), f ∉ x.asIdeal ∧ g ∣ f ∧ f • m = F t := by
  obtain ⟨τ, hτ⟩ := hF.2 (LocalizedModule.mk m 1)
  induction τ using LocalizedModule.induction_on with
  | h t s =>
    rw [LocalizedModule.map_mk, LocalizedModule.mk_eq] at hτ
    obtain ⟨u, hu⟩ := hτ
    simp only [Submonoid.smul_def, one_smul] at hu

    refine ⟨g * ((u : B) * (s : B)), g • (u : B) • t,
      fun h => (x.isPrime.mem_or_mem h).elim hg fun h' => (x.isPrime.mem_or_mem h').elim u.2 s.2, dvd_mul_right g _, ?_⟩
    rw [map_smul, map_smul, hu, mul_smul, mul_smul]

omit [Algebra 𝒪 K] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] [IsFractionRing 𝒪 K] in
theorem one_notMem (x : PrimeSpectrum B) : (1 : B) ∉ x.asIdeal := fun h =>
  x.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr h)

theorem u₀_continuous_loc (hle : M'.1 ≤ M.1) (x : PrimeSpectrum B) (v : Fin 2 → K)
    (hvx : v ∈ (loc₀ d hle x).1.1) :
    ∃ (f : B) (t : T0 d M'), f ∉ x.asIdeal ∧ ∀ (y : PrimeSpectrum B) (hy : f ∉ y.asIdeal),
      ∃ hv : v ∈ (loc₀ d hle y).1.1,
        (loc₀ d hle y).2 ((1 : locRing B y) ⊗ₜ[𝒪] (⟨v, hv⟩ : ↥(loc₀ d hle y).1.1)) = LocalizedModule.mk t ⟨f, hy⟩ := by
  classical
  have hvM : v ∈ M.1 := by
    by_cases hx : x ∈ S0 d (M := M) hle
    · rw [loc₀_fst_of_mem d hle hx] at hvx; exact hle hvx
    · rw [loc₀_fst_of_not_mem d hle hx] at hvx; exact hvx
  by_cases hv' : v ∈ M'.1
  · refine ⟨1, (d.line M').mkQ ((1 : B) ⊗ₜ[𝒪] (⟨v, hv'⟩ : ↥M'.1)), one_notMem x, fun y hy => ?_⟩
    have hvy : v ∈ (loc₀ d hle y).1.1 := by
      by_cases hy0 : y ∈ S0 d (M := M) hle
      · rw [loc₀_fst_of_mem d hle hy0]; exact hv'
      · rw [loc₀_fst_of_not_mem d hle hy0]; exact hle hv'
    refine ⟨hvy, ?_⟩
    rw [show (⟨1, hy⟩ : y.asIdeal.primeCompl) = 1 from Subtype.ext rfl]
    by_cases hy0 : y ∈ S0 d (M := M) hle
    · exact val_loc₀_on d hle hy0 v hvy hv'
    · rw [val_loc₀_off d hle hy0 v hvy (hle hv'), ← Pi0_mkQ_tmul d hle 1 v hv', ← LocalizedModule.map_mk,
        Pi0inv_map_Pi0]
  · have hx0 : x ∉ S0 d (M := M) hle := fun hx => hv' (by rwa [loc₀_fst_of_mem d hle hx] at hvx)
    obtain ⟨g, hg, hgS⟩ := exists_basicOpen_subset_compl (isClosed_S0 d hle) hx0
    obtain ⟨f, t, hf, ⟨c, hc⟩, hft⟩ := exists_section_of_bijective (Pi0 d hle) x
      (Module.Invertible.bijective_localizedModule_map_of_not_range_le (Pi0 d hle) x hx0) g hg
      ((d.line M).mkQ ((1 : B) ⊗ₜ[𝒪] (⟨v, hvM⟩ : ↥M.1)))
    refine ⟨f, t, hf, fun y hy => ?_⟩
    have hgy : g ∉ y.asIdeal := fun h => hy (hc ▸ y.asIdeal.mul_mem_right c h)
    have hy0 : y ∉ S0 d (M := M) hle := hgS y hgy
    have hvy : v ∈ (loc₀ d hle y).1.1 := by rw [loc₀_fst_of_not_mem d hle hy0]; exact hvM
    refine ⟨hvy, ?_⟩
    rw [val_loc₀_off d hle hy0 v hvy hvM]
    have : (LocalizedModule.mk ((d.line M).mkQ ((1 : B) ⊗ₜ[𝒪] (⟨v, hvM⟩ : ↥M.1))) 1 : stalk B y (T1 d M)) =
        LocalizedModule.map y.asIdeal.primeCompl (Pi0 d hle) (LocalizedModule.mk t ⟨f, hy⟩) := by
      rw [LocalizedModule.map_mk, ← hft, LocalizedModule.mk_eq]
      exact ⟨1, by simp only [Submonoid.smul_def, one_smul, Submonoid.coe_one]⟩
    rw [this, Pi0inv_map_Pi0]

theorem u₁_continuous_loc (hπ : Irreducible π) (hle : M'.1 ≤ M.1) (hπM : ∀ v ∈ M.1, algebraMap 𝒪 K π • v ∈ M'.1)
    (x : PrimeSpectrum B) (v : Fin 2 → K) (hvx : v ∈ (loc₁ d hπ hπM x).1.1) :
    ∃ (f : B) (t : T1 d M), f ∉ x.asIdeal ∧ ∀ (y : PrimeSpectrum B) (hy : f ∉ y.asIdeal),
      ∃ hv : v ∈ (loc₁ d hπ hπM y).1.1,
        (loc₁ d hπ hπM y).2 ((1 : locRing B y) ⊗ₜ[𝒪] (⟨v, hv⟩ : ↥(loc₁ d hπ hπM y).1.1)) =
          LocalizedModule.mk t ⟨f, hy⟩ := by
  classical
  have hvP : v ∈ (Mpi (K := K) hπ M').1 := by
    by_cases hx : x ∈ S1 d hπ hπM
    · rw [loc₁_fst_of_mem d hπ hπM hx] at hvx; exact le_Mpi hπ hle hπM hvx
    · rw [loc₁_fst_of_not_mem d hπ hπM hx] at hvx; exact hvx
  have hvπ : algebraMap 𝒪 K π • v ∈ M'.1 := smul_mem_of_mem_Mpi hπ M' v hvP
  by_cases hvM : v ∈ M.1
  · refine ⟨1, (d.line M).mkQ ((1 : B) ⊗ₜ[𝒪] (⟨v, hvM⟩ : ↥M.1)), one_notMem x, fun y hy => ?_⟩
    have hvy : v ∈ (loc₁ d hπ hπM y).1.1 := by
      by_cases hy1 : y ∈ S1 d hπ hπM
      · rw [loc₁_fst_of_mem d hπ hπM hy1]; exact hvM
      · rw [loc₁_fst_of_not_mem d hπ hπM hy1]; exact le_Mpi hπ hle hπM hvM
    refine ⟨hvy, ?_⟩
    rw [show (⟨1, hy⟩ : y.asIdeal.primeCompl) = 1 from Subtype.ext rfl]
    by_cases hy1 : y ∈ S1 d hπ hπM
    · exact val_loc₁_on d hπ hπM hy1 v hvy hvM
    · rw [val_loc₁_off d hπ hπM hy1 v hvy hvπ,
        show (⟨algebraMap 𝒪 K π • v, hvπ⟩ : ↥M'.1) = ⟨algebraMap 𝒪 K π • v, hπM v hvM⟩ from rfl,
        ← Pi1_mkQ_tmul d hπ hπM 1 v hvM, ← LocalizedModule.map_mk, Pi1inv_map_Pi1]
  · have hx1 : x ∉ S1 d hπ hπM := fun hx => hvM (by rwa [loc₁_fst_of_mem d hπ hπM hx] at hvx)
    obtain ⟨g, hg, hgS⟩ := exists_basicOpen_subset_compl (isClosed_S1 d hπ hπM) hx1
    obtain ⟨f, t, hf, ⟨c, hc⟩, hft⟩ := exists_section_of_bijective (Pi1 d hπ hπM) x
      (Module.Invertible.bijective_localizedModule_map_of_not_range_le (Pi1 d hπ hπM) x hx1) g hg
      ((d.line M').mkQ ((1 : B) ⊗ₜ[𝒪] (⟨algebraMap 𝒪 K π • v, hvπ⟩ : ↥M'.1)))
    refine ⟨f, t, hf, fun y hy => ?_⟩
    have hgy : g ∉ y.asIdeal := fun h => hy (hc ▸ y.asIdeal.mul_mem_right c h)
    have hy1 : y ∉ S1 d hπ hπM := hgS y hgy
    have hvy : v ∈ (loc₁ d hπ hπM y).1.1 := by rw [loc₁_fst_of_not_mem d hπ hπM hy1]; exact hvP
    refine ⟨hvy, ?_⟩
    rw [val_loc₁_off d hπ hπM hy1 v hvy hvπ]
    have : (LocalizedModule.mk ((d.line M').mkQ ((1 : B) ⊗ₜ[𝒪] (⟨algebraMap 𝒪 K π • v, hvπ⟩ : ↥M'.1))) 1 :
        stalk B y (T0 d M')) =
        LocalizedModule.map y.asIdeal.primeCompl (Pi1 d hπ hπM) (LocalizedModule.mk t ⟨f, hy⟩) := by
      rw [LocalizedModule.map_mk, ← hft, LocalizedModule.mk_eq]
      exact ⟨1, by simp only [Submonoid.smul_def, one_smul, Submonoid.coe_one]⟩
    rw [this, Pi1inv_map_Pi1]

theorem locallyConstant_loc₀ (hle : M'.1 ≤ M.1) (x : PrimeSpectrum B) (hx : x ∈ S0 d (M := M) hle) :
    ∃ U : Set (PrimeSpectrum B), IsOpen U ∧ x ∈ U ∧
      ∀ y ∈ U, y ∈ S0 d (M := M) hle → (loc₀ d hle y).1.1 = (loc₀ d hle x).1.1 :=
  ⟨Set.univ, isOpen_univ, Set.mem_univ x, fun y _ hy => by
    rw [loc₀_fst_of_mem d hle hy, loc₀_fst_of_mem d hle hx]⟩

theorem locallyConstant_loc₁ (hπ : Irreducible π) (hπM : ∀ v ∈ M.1, algebraMap 𝒪 K π • v ∈ M'.1)
    (x : PrimeSpectrum B) (hx : x ∈ S1 d hπ hπM) :
    ∃ U : Set (PrimeSpectrum B), IsOpen U ∧ x ∈ U ∧
      ∀ y ∈ U, y ∈ S1 d hπ hπM → (loc₁ d hπ hπM y).1.1 = (loc₁ d hπ hπM x).1.1 :=
  ⟨Set.univ, isOpen_univ, Set.mem_univ x, fun y _ hy => by
    rw [loc₁_fst_of_mem d hπ hπM hy, loc₁_fst_of_mem d hπ hπM hx]⟩

end Local

namespace B25X2

section DetAux

variable {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K]
  [IsFractionRing 𝒪 K]

theorem exists_det_eq_mul (g₁ g₂ : Matrix.GeneralLinearGroup (Fin 2) K)
    (h : latticeMap g₁ (stdLattice 𝒪 K) = latticeMap g₂ (stdLattice 𝒪 K)) :
    ∃ w : 𝒪ˣ, ((Matrix.GeneralLinearGroup.det g₂ : Kˣ) : K) = (Matrix.GeneralLinearGroup.det g₁ : Kˣ) * algebraMap 𝒪 K w := by
  have hfix : latticeMap (g₁⁻¹ * g₂) (stdLattice 𝒪 K) = stdLattice 𝒪 K := by
    rw [latticeMap_mul, ← h, latticeMap_inv_latticeMap]
  obtain ⟨N, hN⟩ := (latticeMap_stdLattice_eq_iff_mem_range _).mp hfix
  refine ⟨Matrix.GeneralLinearGroup.det N, ?_⟩
  have hdet : Matrix.GeneralLinearGroup.det g₂ = Matrix.GeneralLinearGroup.det g₁ * Matrix.GeneralLinearGroup.det (g₁⁻¹ * g₂) := by
    rw [← map_mul, mul_inv_cancel_left]
  have hdetk : ((Matrix.GeneralLinearGroup.det (g₁⁻¹ * g₂) : Kˣ) : K) = algebraMap 𝒪 K (Matrix.GeneralLinearGroup.det N : 𝒪ˣ) := by
    rw [← hN, Matrix.GeneralLinearGroup.val_det_apply, Matrix.GeneralLinearGroup.val_det_apply]
    show ((N : Matrix (Fin 2) (Fin 2) 𝒪).map (algebraMap 𝒪 K)).det = _
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
  rw [hdet, Units.val_mul, hdetk]

end DetAux

section SmulTop

variable {B : Type} [CommRing B]

theorem smul_top_ne_top {L : Type} [AddCommGroup L] [Module B L] [Module.Invertible B L] (x : PrimeSpectrum B) :
    (x.asIdeal • ⊤ : Submodule B L) ≠ ⊤ := by
  intro htop
  have hsub : Subsingleton (L ⧸ (x.asIdeal • ⊤ : Submodule B L)) :=
    Submodule.Quotient.subsingleton_iff.mpr htop
  have hsub' : Subsingleton ((B ⧸ x.asIdeal) ⊗[B] L) :=
    (TensorProduct.quotTensorEquivQuotSMul L x.asIdeal).toEquiv.subsingleton
  haveI : Nontrivial (B ⧸ x.asIdeal) := Ideal.Quotient.nontrivial_iff.mpr x.isPrime.ne_top
  have h01 : (0 : B ⧸ x.asIdeal) = 1 :=
    (FaithfulSMul.eq_of_smul_eq_smul (M := B ⧸ x.asIdeal) (α := (B ⧸ x.asIdeal) ⊗[B] L)
      (fun m => hsub'.elim _ _))
  exact zero_ne_one h01

end SmulTop

section Det

variable {𝒪 : Type} [CommRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K]
variable {B : Type} [CommRing B] [Algebra 𝒪 B]
variable [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] [IsFractionRing 𝒪 K] {π : 𝒪}
variable {M' M : FullLattice 𝒪 K} (d : DeligneDatum (K := K) π B)

open X2Body

theorem hasDetIndex₀_loc (hπ : Irreducible π) (hle : M'.1 ≤ M.1) (hπM : ∀ v ∈ M.1, algebraMap 𝒪 K π • v ∈ M'.1)
    (h0 : HasDetIndex π M'.1 0) (hd : d.InEdgeChart π M' M) (x : PrimeSpectrum B)
    (hx : LinearMap.range (Pi0 d hle) ≤ x.asIdeal • (⊤ : Submodule B (T1 d M))) :
    HasDetIndex π (loc₀ d hle x).1.1 0 := by
  rw [loc₀_fst_of_mem d hle hx]
  exact h0

theorem hasDetIndex₁_loc (hπ : Irreducible π) (hle : M'.1 ≤ M.1) (hπM : ∀ v ∈ M.1, algebraMap 𝒪 K π • v ∈ M'.1)
    (hB : IsNilpotent (algebraMap 𝒪 B π)) (h0 : HasDetIndex π M'.1 0) (hd : d.InEdgeChart π M' M)
    (hMM : M'.1 ≠ M.1) (x : PrimeSpectrum B)
    (hx : LinearMap.range (Pi1 d hπ hπM) ≤ x.asIdeal • (⊤ : Submodule B (T0 d M'))) :
    HasDetIndex π (loc₁ d hπ hπM x).1.1 (-1) := by
  rw [loc₁_fst_of_mem d hπ hπM hx]

  have hπle : latticeMap (scalarGL (unitOfNeZero (K := K) hπ.ne_zero)) M.1 ≤ M'.1 := by
    intro v hv
    obtain ⟨w, hw, rfl⟩ := mem_latticeMap_scalarGL.mp hv
    rw [unitOfNeZero_coe]; exact hπM w hw
  have hne : latticeMap (scalarGL (unitOfNeZero (K := K) hπ.ne_zero)) M.1 ≠ M'.1 := by
    intro hEq
    have hs : Function.Surjective (smulInto π hπM) := by
      intro w
      have hw : (w : Fin 2 → K) ∈ latticeMap (scalarGL (unitOfNeZero (K := K) hπ.ne_zero)) M.1 := hEq.symm ▸ w.2
      obtain ⟨v, hv, hvw⟩ := mem_latticeMap_scalarGL.mp hw
      refine ⟨⟨v, hv⟩, Subtype.ext ?_⟩
      rw [coe_smulInto_apply, ← hvw, unitOfNeZero_coe]
    have hs' : Function.Surjective ((smulInto π hπM).baseChange B) := by
      rw [LinearMap.baseChange_eq_ltensor]; exact LinearMap.lTensor_surjective B hs
    have hsurj : Function.Surjective (Pi1 d hπ hπM) := by
      intro t
      obtain ⟨z, rfl⟩ := Submodule.mkQ_surjective _ t
      obtain ⟨y, rfl⟩ := hs' z
      exact ⟨Submodule.Quotient.mk y, rfl⟩
    have htop : (x.asIdeal • ⊤ : Submodule B (T0 d M')) = ⊤ :=
      eq_top_iff.mpr (le_trans (LinearMap.range_eq_top.mpr hsurj).ge hx)
    exact smul_top_ne_top x htop

  have h1lt : latticeMap (scalarGL (unitOfNeZero (K := K) hπ.ne_zero)) M.1 < M'.1 := lt_of_le_of_ne hπle hne
  have h2lt : M'.1 < M.1 := lt_of_le_of_ne hle hMM
  obtain ⟨h, hM, hM'⟩ := CerednikDrinfeld.FormalOmega.exists_act_stdFullLattice_eq_and_act_act_eq_of_lt_of_lt π hπ
    (diagFst K (unitOfNeZero (K := K) hπ.ne_zero)) (by rw [diagFst_coe, unitOfNeZero_coe]) M' M h1lt h2lt
  have hMv : latticeMap h (stdLattice 𝒪 K) = M.1 := congrArg Subtype.val hM
  have hM'v : latticeMap (h * diagFst K (unitOfNeZero (K := K) hπ.ne_zero)) (stdLattice 𝒪 K) = M'.1 := by
    rw [latticeMap_mul]; exact congrArg Subtype.val hM'
  obtain ⟨g₀, hg₀, u₀, hu₀⟩ := h0
  obtain ⟨w, hw⟩ := exists_det_eq_mul g₀ (h * diagFst K (unitOfNeZero (K := K) hπ.ne_zero)) (hg₀.trans hM'v.symm)

  have hdg : ((Matrix.GeneralLinearGroup.det (diagFst K (unitOfNeZero (K := K) hπ.ne_zero)) : Kˣ) : K) =
      algebraMap 𝒪 K π := by
    rw [Matrix.GeneralLinearGroup.val_det_apply, diagFst_coe, Matrix.det_diagonal, unitOfNeZero_coe]
    simp [Fin.prod_univ_two]
  have hπK : algebraMap 𝒪 K π ≠ 0 := fun h0' => hπ.ne_zero (IsFractionRing.injective 𝒪 K (by rw [h0', map_zero]))
  refine ⟨h, hMv, u₀ * w, ?_⟩
  rw [map_mul, Units.val_mul, hdg, hu₀, zpow_zero, mul_one] at hw
  rw [zpow_neg_one, Units.val_mul, map_mul, eq_mul_inv_iff_mul_eq₀ hπK, hw]

end Det

end B25X2

section Local2
variable [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] [IsFractionRing 𝒪 K] {π : 𝒪}
variable {M' M : FullLattice 𝒪 K} (d : DeligneDatum (K := K) π B)

theorem not_mem_smul_top_of_bijective {P Q : Type} [AddCommGroup P] [Module B P] [AddCommGroup Q] [Module B Q]
    [Module.Invertible B P] [Module.Invertible B Q] (f : P →ₗ[B] Q) (x : PrimeSpectrum B)
    (hf : Function.Bijective (LocalizedModule.map x.asIdeal.primeCompl f)) (t : P)
    (ht : t ∉ x.asIdeal • (⊤ : Submodule B P)) : f t ∉ x.asIdeal • (⊤ : Submodule B Q) := by
  intro hft
  apply ht
  apply mem_smul_top_of_forall_form
  intro φ
  let e := LinearEquiv.ofBijective (LocalizedModule.map x.asIdeal.primeCompl f) hf

  have h1 : (LocalizedModule.mk (f t) 1 : LocalizedModule x.asIdeal.primeCompl Q) ∈
      x.asIdeal • (⊤ : Submodule B (LocalizedModule x.asIdeal.primeCompl Q)) := by
    have := Submodule.mem_map_of_mem (f := LocalizedModule.mkLinearMap x.asIdeal.primeCompl Q) hft
    rw [Submodule.map_smul'', Submodule.map_top, LocalizedModule.mkLinearMap_apply] at this
    exact Submodule.smul_mono le_rfl le_top this

  have h2 : (LocalizedModule.mk t 1 : LocalizedModule x.asIdeal.primeCompl P) ∈
      x.asIdeal • (⊤ : Submodule B (LocalizedModule x.asIdeal.primeCompl P)) := by
    have he : e.symm (LocalizedModule.mk (f t) 1) = LocalizedModule.mk t 1 := by
      rw [LinearEquiv.symm_apply_eq, LinearEquiv.ofBijective_apply, LocalizedModule.map_mk]
    have := Submodule.mem_map_of_mem (f := (e.symm.toLinearMap.restrictScalars B)) h1
    rw [Submodule.map_smul'', Submodule.map_top] at this
    have := Submodule.smul_mono (le_refl x.asIdeal) (le_top (a := LinearMap.range _)) this
    rwa [LinearMap.restrictScalars_apply, LinearEquiv.coe_coe, he] at this

  have h3 : (LocalizedModule.mk (φ t) 1 : LocalizedModule x.asIdeal.primeCompl B) ∈
      x.asIdeal • (⊤ : Submodule B (LocalizedModule x.asIdeal.primeCompl B)) := by
    have := Submodule.mem_map_of_mem (f := (LocalizedModule.map x.asIdeal.primeCompl φ).restrictScalars B) h2
    rw [Submodule.map_smul'', Submodule.map_top] at this
    have := Submodule.smul_mono (le_refl x.asIdeal) (le_top (a := LinearMap.range _)) this
    rwa [LinearMap.restrictScalars_apply, LocalizedModule.map_mk] at this
  exact mem_of_mk_mem_smul_top x (φ t) h3

theorem not_mem_sup_iff_mkQ_not_mem (x : PrimeSpectrum B) (L : FullLattice 𝒪 K) (N : Submodule B (latticeBaseChange 𝒪 K B L))
    (y : latticeBaseChange 𝒪 K B L) :
    y ∉ N ⊔ (x.asIdeal • ⊤ : Submodule B (latticeBaseChange 𝒪 K B L)) ↔
      N.mkQ y ∉ (x.asIdeal • ⊤ : Submodule B (latticeBaseChange 𝒪 K B L ⧸ N)) := by
  rw [not_iff_not]
  constructor
  · intro hy
    have : N.mkQ y ∈ ((x.asIdeal • ⊤ : Submodule B (latticeBaseChange 𝒪 K B L)) ⊔ N).map N.mkQ :=
      Submodule.mem_map_of_mem (by rwa [sup_comm] at hy)
    rwa [Submodule.map_sup, Submodule.map_smul'', Submodule.map_top, Submodule.range_mkQ, Submodule.mkQ_map_self,
      sup_bot_eq] at this
  · intro hy
    have hmap : (x.asIdeal • ⊤ : Submodule B (latticeBaseChange 𝒪 K B L ⧸ N)) =
        (x.asIdeal • (⊤ : Submodule B (latticeBaseChange 𝒪 K B L))).map N.mkQ := by
      rw [Submodule.map_smul'', Submodule.map_top, Submodule.range_mkQ]
    have : y ∈ ((x.asIdeal • (⊤ : Submodule B (latticeBaseChange 𝒪 K B L))).map N.mkQ).comap N.mkQ := by
      rw [← hmap]; exact hy
    rwa [Submodule.comap_map_mkQ] at this

theorem not_mem_sup_incl_of_not_mem_S0 (hle : M'.1 ≤ M.1) (x : PrimeSpectrum B) (hx : x ∉ S0 d (M := M) hle)
    (y : latticeBaseChange 𝒪 K B M')
    (hy : y ∉ d.line M' ⊔ (x.asIdeal • ⊤ : Submodule B (latticeBaseChange 𝒪 K B M'))) :
    inclBaseChange B hle y ∉ d.line M ⊔ (x.asIdeal • ⊤ : Submodule B (latticeBaseChange 𝒪 K B M)) := by
  rw [not_mem_sup_iff_mkQ_not_mem x] at hy ⊢
  have h := not_mem_smul_top_of_bijective (Pi0 d hle) x
    (Module.Invertible.bijective_localizedModule_map_of_not_range_le (Pi0 d hle) x hx) _ hy
  rwa [Pi0, Submodule.mkQ_apply, Submodule.mapQ_apply] at h

theorem not_mem_sup_smul_of_not_mem_S1 (hπ : Irreducible π) (hπM : ∀ v ∈ M.1, algebraMap 𝒪 K π • v ∈ M'.1)
    (x : PrimeSpectrum B) (hx : x ∉ S1 d hπ hπM) (y : latticeBaseChange 𝒪 K B M)
    (hy : y ∉ d.line M ⊔ (x.asIdeal • ⊤ : Submodule B (latticeBaseChange 𝒪 K B M))) :
    (smulInto π hπM).baseChange B y ∉ d.line M' ⊔ (x.asIdeal • ⊤ : Submodule B (latticeBaseChange 𝒪 K B M')) := by
  rw [not_mem_sup_iff_mkQ_not_mem x] at hy ⊢
  have h := not_mem_smul_top_of_bijective (Pi1 d hπ hπM) x
    (Module.Invertible.bijective_localizedModule_map_of_not_range_le (Pi1 d hπ hπM) x hx) _ hy
  rwa [Pi1, Submodule.mkQ_apply, Submodule.mapQ_apply] at h

theorem not_exists_eq_smul_of_not_mem (hπ : Irreducible π) {L : Submodule 𝒪 (Fin 2 → K)} {v : Fin 2 → K}
    (hv : v ∉ L) : ¬ ∃ w : ↥L, algebraMap 𝒪 K π • v = algebraMap 𝒪 K π • (w : Fin 2 → K) := by
  rintro ⟨w, h⟩
  apply hv
  rw [smul_right_injective (Fin 2 → K) (hπK_of_irreducible (K := K) hπ) h]
  exact w.2

theorem exists_eq_smul_Mpi (hπ : Irreducible π) (M' : FullLattice 𝒪 K) (v' : ↥M'.1) :
    ∃ w : ↥(Mpi (K := K) hπ M').1, (v' : Fin 2 → K) = algebraMap 𝒪 K π • (w : Fin 2 → K) := by
  refine ⟨⟨((piUnit (K := K) hπ)⁻¹ : Kˣ) • (v' : Fin 2 → K), ?_⟩, ?_⟩
  · exact mem_latticeMap_scalarGL.mpr ⟨v', v'.2, rfl⟩
  · show (v' : Fin 2 → K) = algebraMap 𝒪 K π • ((((piUnit (K := K) hπ)⁻¹ : Kˣ) : K) • (v' : Fin 2 → K))
    rw [smul_smul, Units.val_inv_eq_inv_val, show algebraMap 𝒪 K π = ((piUnit (K := K) hπ : Kˣ) : K) from rfl,
      mul_inv_cancel₀ (piUnit (K := K) hπ).ne_zero, one_smul]

theorem smulEquiv_baseChange_coe (hπ : Irreducible π) (M' : FullLattice 𝒪 K) :
    (((smulEquiv (K := K) hπ M').baseChange 𝒪 B _ _ :
      latticeBaseChange 𝒪 K B (Mpi (K := K) hπ M') ≃ₗ[B] latticeBaseChange 𝒪 K B M') :
      latticeBaseChange 𝒪 K B (Mpi (K := K) hπ M') →ₗ[B] latticeBaseChange 𝒪 K B M') =
      (smulInto π (smul_mem_of_mem_Mpi (K := K) hπ M')).baseChange B := by
  refine TensorProduct.AlgebraTensorModule.ext fun b v => ?_
  rw [LinearEquiv.coe_coe, LinearEquiv.baseChange_tmul, LinearMap.baseChange_tmul]
  rfl

theorem one_tmul_mem_sup_Mpi_iff (hπ : Irreducible π) (M' : FullLattice 𝒪 K) (I : Ideal B)
    (v : ↥(Mpi (K := K) hπ M').1) :
    (1 : B) ⊗ₜ[𝒪] v ∈ d.line (Mpi (K := K) hπ M') ⊔ (I • ⊤ : Submodule B (latticeBaseChange 𝒪 K B (Mpi (K := K) hπ M'))) ↔
      (1 : B) ⊗ₜ[𝒪] (smulInto π (smul_mem_of_mem_Mpi (K := K) hπ M') v) ∈
        d.line M' ⊔ (I • ⊤ : Submodule B (latticeBaseChange 𝒪 K B M')) := by
  set e : latticeBaseChange 𝒪 K B (Mpi (K := K) hπ M') ≃ₗ[B] latticeBaseChange 𝒪 K B M' :=
    (smulEquiv (K := K) hπ M').baseChange 𝒪 B _ _ with he_def
  have he : (e : latticeBaseChange 𝒪 K B (Mpi (K := K) hπ M') →ₗ[B] latticeBaseChange 𝒪 K B M') =
      (smulInto π (smul_mem_of_mem_Mpi (K := K) hπ M')).baseChange B := by
    rw [he_def]; exact smulEquiv_baseChange_coe hπ M'
  have hmap : (d.line (Mpi (K := K) hπ M') ⊔ (I • ⊤ : Submodule B (latticeBaseChange 𝒪 K B (Mpi (K := K) hπ M')))).map
      (e : latticeBaseChange 𝒪 K B (Mpi (K := K) hπ M') →ₗ[B] latticeBaseChange 𝒪 K B M') =
      d.line M' ⊔ (I • ⊤ : Submodule B (latticeBaseChange 𝒪 K B M')) := by
    rw [Submodule.map_sup, Submodule.map_smul'', Submodule.map_top, LinearEquiv.range, he,
      map_smulInto_line_Mpi d hπ M']
  have hev : e ((1 : B) ⊗ₜ[𝒪] v) = (1 : B) ⊗ₜ[𝒪] (smulInto π (smul_mem_of_mem_Mpi (K := K) hπ M') v) := by
    rw [← LinearEquiv.coe_coe, he, LinearMap.baseChange_tmul]
  rw [← hmap, ← hev, Submodule.map_equiv_eq_comap_symm, Submodule.mem_comap, LinearEquiv.coe_coe,
    LinearEquiv.symm_apply_apply]

theorem not_mem_sup_Mpi_of (hπ : Irreducible π) (M' : FullLattice 𝒪 K) (I : Ideal B) (v : ↥(Mpi (K := K) hπ M').1)
    (h : (1 : B) ⊗ₜ[𝒪] (smulInto π (smul_mem_of_mem_Mpi (K := K) hπ M') v) ∉
      d.line M' ⊔ (I • ⊤ : Submodule B (latticeBaseChange 𝒪 K B M'))) :
    (1 : B) ⊗ₜ[𝒪] v ∉
      d.line (Mpi (K := K) hπ M') ⊔ (I • ⊤ : Submodule B (latticeBaseChange 𝒪 K B (Mpi (K := K) hπ M'))) :=
  fun hv => h ((one_tmul_mem_sup_Mpi_iff d hπ M' I v).mp hv)

theorem inEdgeChart_Mpi_of_inEdgeChart_self (hπ : Irreducible π) (M' : FullLattice 𝒪 K)
    (hπM : ∀ v ∈ M'.1, algebraMap 𝒪 K π • v ∈ M'.1) (hd : d.InEdgeChart π M' M') :
    d.InEdgeChart π M' (Mpi (K := K) hπ M') := by
  intro 𝔭 h𝔭
  have hdx := hd 𝔭 h𝔭
  refine ⟨le_Mpi hπ le_rfl hπM, fun v => smul_mem_of_mem_Mpi (K := K) hπ M' v v.2, ?_, ?_⟩
  · intro v hv
    refine not_mem_sup_Mpi_of d hπ M' 𝔭 v (hdx.2.2.2 _ ?_)
    rw [coe_smulInto_apply]
    exact not_exists_eq_smul_of_not_mem hπ hv
  · intro v' hv'
    exact (hv' (exists_eq_smul_Mpi hπ M' v')).elim

theorem fst_ne_Mpi_fst (hπ : Irreducible π) (M' : FullLattice 𝒪 K) (h0 : HasDetIndex π M'.1 0) :
    M'.1 ≠ (Mpi (K := K) hπ M').1 := by
  intro heq
  obtain ⟨g₀, hg₀, u, hu⟩ := h0
  have h' : latticeMap g₀ (stdLattice 𝒪 K) = latticeMap (scalarGL (piUnit (K := K) hπ)⁻¹ * g₀) (stdLattice 𝒪 K) := by
    rw [latticeMap_mul, hg₀]; exact heq
  obtain ⟨w, hw⟩ := B25X2.exists_det_eq_mul g₀ _ h'
  have hdet : ((Matrix.GeneralLinearGroup.det (scalarGL (piUnit (K := K) hπ)⁻¹) : Kˣ) : K) =
      (((piUnit (K := K) hπ)⁻¹ : Kˣ) : K) ^ 2 := by
    rw [Matrix.GeneralLinearGroup.val_det_apply, scalarGL_coe, Matrix.det_smul, Matrix.det_one, mul_one,
      Fintype.card_fin]
  rw [map_mul, Units.val_mul, hdet, mul_comm] at hw
  have h1 : (((piUnit (K := K) hπ)⁻¹ : Kˣ) : K) ^ 2 = algebraMap 𝒪 K w :=
    mul_left_cancel₀ (Matrix.GeneralLinearGroup.det g₀).ne_zero hw
  refine hπ.not_isUnit (isUnit_of_algebraMap_mul_eq_one (K := K) (w := algebraMap 𝒪 K π * algebraMap 𝒪 K w)
    ⟨π * w, by rw [map_mul]⟩ ?_)
  rw [← h1, ← mul_assoc, ← pow_two, Units.val_inv_eq_inv_val, inv_pow,
    show algebraMap 𝒪 K π = ((piUnit (K := K) hπ : Kˣ) : K) from rfl,
    mul_inv_cancel₀ (pow_ne_zero 2 (piUnit (K := K) hπ).ne_zero)]

theorem edgeNondegAt_loc (hπ : Irreducible π) (hle : M'.1 ≤ M.1) (hπM : ∀ v ∈ M.1, algebraMap 𝒪 K π • v ∈ M'.1)
    (hB : IsNilpotent (algebraMap 𝒪 B π)) (hd : d.InEdgeChart π M' M) (x : PrimeSpectrum B) :
    d.EdgeNondegAt π x.asIdeal (loc₀ d hle x).1 (loc₁ d hπ hπM x).1 := by
  classical
  have hdx := hd x.asIdeal x.isPrime
  by_cases h0 : x ∈ S0 d (M := M) hle <;> by_cases h1 : x ∈ S1 d hπ hπM
  ·
    rw [loc₀_eq_of_mem d hle h0, loc₁_eq_of_mem d hπ hπM h1]; exact hdx
  ·
    rw [loc₀_eq_of_mem d hle h0, loc₁_eq_of_not_mem d hπ hπM h1]
    refine ⟨hle.trans (le_Mpi hπ hle hπM), fun v => smul_mem_of_mem_Mpi hπ M' v v.2, ?_, ?_⟩
    ·
      intro v hv
      apply not_mem_sup_Mpi_of d hπ M' x.asIdeal v
      by_cases hvM : (v : Fin 2 → K) ∈ M.1
      ·
        have h := not_mem_sup_smul_of_not_mem_S1 d hπ hπM x h1 _ (hdx.2.2.1 ⟨v, hvM⟩ hv)
        have hw : smulInto π hπM ⟨(v : Fin 2 → K), hvM⟩ = smulInto π (smul_mem_of_mem_Mpi (K := K) hπ M') v :=
          Subtype.ext rfl
        rwa [LinearMap.baseChange_tmul, hw] at h
      ·
        exact hdx.2.2.2 _ (by rw [coe_smulInto_apply]; exact not_exists_eq_smul_of_not_mem hπ hvM)
    · intro v' hv'
      exfalso; apply hv'

      refine ⟨⟨((piUnit (K := K) hπ)⁻¹ : Kˣ) • (v' : Fin 2 → K), ?_⟩, ?_⟩
      · exact mem_latticeMap_scalarGL.mpr ⟨v', v'.2, rfl⟩
      · show (v' : Fin 2 → K) = algebraMap 𝒪 K π • ((((piUnit (K := K) hπ)⁻¹ : Kˣ) : K) • (v' : Fin 2 → K))
        rw [smul_smul, Units.val_inv_eq_inv_val, show algebraMap 𝒪 K π = ((piUnit (K := K) hπ : Kˣ) : K) from rfl,
          mul_inv_cancel₀ (piUnit (K := K) hπ).ne_zero, one_smul]
  ·
    rw [loc₀_eq_of_not_mem d hle h0, loc₁_eq_of_mem d hπ hπM h1]
    refine ⟨le_rfl, fun v => hle (hπM v v.2), fun v hv => (hv v.2).elim, ?_⟩
    intro v' hv'
    by_cases hvM' : (v' : Fin 2 → K) ∈ M'.1
    · have h4 := hdx.2.2.2 ⟨v', hvM'⟩ hv'
      have h := not_mem_sup_incl_of_not_mem_S0 d hle x h0 _ h4
      rwa [inclBaseChange, LinearMap.baseChange_tmul] at h
    · exact hdx.2.2.1 v' hvM'
  · exact ((mem_S0_or_mem_S1 d hπ hle hπM hB x).elim h0 h1).elim

theorem loc_smul_mem_smul_top {Q : Type} [AddCommGroup Q] [Module B Q] (x : PrimeSpectrum B) (r : locRing B x)
    (m : stalk B x Q) (hm : m ∈ x.asIdeal • (⊤ : Submodule B (stalk B x Q))) :
    r • m ∈ x.asIdeal • (⊤ : Submodule B (stalk B x Q)) := by
  refine Submodule.smul_induction_on hm ?_ ?_
  · intro p hp n _
    rw [← algebraMap_smul (locRing B x) p n, smul_smul, mul_comm, ← smul_smul, algebraMap_smul]
    exact Submodule.smul_mem_smul hp Submodule.mem_top
  · intro a b ha hb
    rw [smul_add]
    exact Submodule.add_mem _ ha hb

theorem range_map_le_smul_top {P Q : Type} [AddCommGroup P] [Module B P] [AddCommGroup Q] [Module B Q]
    (f : P →ₗ[B] Q) (x : PrimeSpectrum B) (hf : LinearMap.range f ≤ x.asIdeal • (⊤ : Submodule B Q)) :
    (LinearMap.range (LocalizedModule.map x.asIdeal.primeCompl f)).restrictScalars B ≤
      x.asIdeal • (⊤ : Submodule B (stalk B x Q)) := by
  rintro m ⟨t, rfl⟩
  induction t using LocalizedModule.induction_on with
  | h p s =>
    rw [LocalizedModule.map_mk]
    have h1 : (LocalizedModule.mk (f p) 1 : stalk B x Q) ∈ x.asIdeal • (⊤ : Submodule B (stalk B x Q)) := by
      have := Submodule.mem_map_of_mem (f := LocalizedModule.mkLinearMap x.asIdeal.primeCompl Q) (hf ⟨p, rfl⟩)
      rw [Submodule.map_smul'', Submodule.map_top, LocalizedModule.mkLinearMap_apply] at this
      exact Submodule.smul_mono le_rfl le_top this
    have h2 : (LocalizedModule.mk (f p) s : stalk B x Q) =
        (Localization.mk 1 s : locRing B x) • (LocalizedModule.mk (f p) 1 : stalk B x Q) := by
      rw [LocalizedModule.mk_smul_mk, one_smul, mul_one]
    rw [h2]
    exact loc_smul_mem_smul_top x _ _ h1

theorem mem_smul_top_of_mk_mem {Q : Type} [AddCommGroup Q] [Module B Q] [Module.Invertible B Q] (x : PrimeSpectrum B)
    (q : Q) (hq : (LocalizedModule.mk q 1 : stalk B x Q) ∈ x.asIdeal • (⊤ : Submodule B (stalk B x Q))) :
    q ∈ x.asIdeal • (⊤ : Submodule B Q) := by
  apply mem_smul_top_of_forall_form
  intro φ
  have := Submodule.mem_map_of_mem (f := (LocalizedModule.map x.asIdeal.primeCompl φ).restrictScalars B) hq
  rw [Submodule.map_smul'', Submodule.map_top] at this
  have := Submodule.smul_mono (le_refl x.asIdeal) (le_top (a := LinearMap.range _)) this
  rw [LinearMap.restrictScalars_apply, LocalizedModule.map_mk] at this
  exact mem_of_mk_mem_smul_top x (φ q) this

theorem one_tmul_mem_sup_of_stalkQuot_mem (x : PrimeSpectrum B) (L : FullLattice 𝒪 K) (v : ↥L.1)
    (h : stalkQuot x L (d.line L) ((1 : locRing B x) ⊗ₜ[𝒪] v) ∈ x.asIdeal • (⊤ : Submodule B (stalk B x (T0 d L)))) :
    (1 : B) ⊗ₜ[𝒪] v ∈ d.line L ⊔ (x.asIdeal • ⊤ : Submodule B (latticeBaseChange 𝒪 K B L)) := by
  by_contra hc
  rw [not_mem_sup_iff_mkQ_not_mem x] at hc
  apply hc
  rw [stalkQuot_one_tmul, LocalizedModule.mkLinearMap_apply] at h
  exact mem_smul_top_of_mk_mem x _ h

theorem injective₀_loc (hπ : Irreducible π) (hle : M'.1 ≤ M.1) (hπM : ∀ v ∈ M.1, algebraMap 𝒪 K π • v ∈ M'.1)
    (hB : IsNilpotent (algebraMap 𝒪 B π)) (hd : d.InEdgeChart π M' M) (x : PrimeSpectrum B)
    (v : ↥(loc₀ d hle x).1.1)
    (hv : (loc₀ d hle x).2 ((1 : locRing B x) ⊗ₜ[𝒪] v) ∈
      (LinearMap.range (LocalizedModule.map x.asIdeal.primeCompl (Pi1 d hπ hπM))).restrictScalars B ⊔
        x.asIdeal • (⊤ : Submodule B (stalk B x (T0 d M')))) :
    ∃ w ∈ (loc₁ d hπ hπM x).1.1, (v : Fin 2 → K) = algebraMap 𝒪 K π • w := by
  classical
  have hdx := hd x.asIdeal x.isPrime
  by_cases h0 : x ∈ S0 d (M := M) hle <;> by_cases h1 : x ∈ S1 d hπ hπM
  ·
    revert v hv
    rw [loc₀_eq_of_mem d hle h0, loc₁_eq_of_mem d hπ hπM h1]
    intro v hv
    have hv' := (sup_le (range_map_le_smul_top (Pi1 d hπ hπM) x h1) le_rfl) hv
    have hmem := one_tmul_mem_sup_of_stalkQuot_mem d x M' v hv'
    by_contra hne
    exact hdx.2.2.2 v (fun ⟨w, hw⟩ => hne ⟨w, w.2, hw⟩) hmem
  ·
    revert v hv
    rw [loc₀_eq_of_mem d hle h0, loc₁_eq_of_not_mem d hπ hπM h1]
    intro v _
    refine ⟨(((piUnit (K := K) hπ)⁻¹ : Kˣ) : K) • (v : Fin 2 → K), mem_latticeMap_scalarGL.mpr ⟨v, v.2, rfl⟩, ?_⟩
    rw [smul_smul, Units.val_inv_eq_inv_val, show algebraMap 𝒪 K π = ((piUnit (K := K) hπ : Kˣ) : K) from rfl,
      mul_inv_cancel₀ (piUnit (K := K) hπ).ne_zero, one_smul]
  ·
    revert v hv
    rw [loc₀_eq_of_not_mem d hle h0, loc₁_eq_of_mem d hπ hπM h1]
    intro v hv
    have hv' := (sup_le (range_map_le_smul_top (Pi1 d hπ hπM) x h1) le_rfl) hv
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe] at hv'
    have hv'' : stalkQuot x M (d.line M) ((1 : locRing B x) ⊗ₜ[𝒪] v) ∈
        x.asIdeal • (⊤ : Submodule B (stalk B x (T1 d M))) := by
      have := Submodule.mem_map_of_mem
        (f := (LocalizedModule.map x.asIdeal.primeCompl (Pi0 d hle)).restrictScalars B) hv'
      rw [Submodule.map_smul'', Submodule.map_top] at this
      have := Submodule.smul_mono (le_refl x.asIdeal) (le_top (a := LinearMap.range _)) this
      rwa [LinearMap.restrictScalars_apply, map_Pi0_Pi0inv] at this
    have hmem := one_tmul_mem_sup_of_stalkQuot_mem d x M v hv''
    have hvM' : (v : Fin 2 → K) ∈ M'.1 := by
      by_contra h
      exact hdx.2.2.1 v h hmem
    by_contra hne
    have h4 := hdx.2.2.2 ⟨v, hvM'⟩ (fun ⟨w, hw⟩ => hne ⟨w, w.2, hw⟩)
    have h5 := not_mem_sup_incl_of_not_mem_S0 d hle x h0 _ h4
    rw [inclBaseChange, LinearMap.baseChange_tmul] at h5
    exact h5 hmem
  · exact ((mem_S0_or_mem_S1 d hπ hle hπM hB x).elim h0 h1).elim

theorem injective₁_loc (hπ : Irreducible π) (hle : M'.1 ≤ M.1) (hπM : ∀ v ∈ M.1, algebraMap 𝒪 K π • v ∈ M'.1)
    (hB : IsNilpotent (algebraMap 𝒪 B π)) (hd : d.InEdgeChart π M' M) (x : PrimeSpectrum B)
    (v : ↥(loc₁ d hπ hπM x).1.1)
    (hv : (loc₁ d hπ hπM x).2 ((1 : locRing B x) ⊗ₜ[𝒪] v) ∈
      (LinearMap.range (LocalizedModule.map x.asIdeal.primeCompl (Pi0 d hle))).restrictScalars B ⊔
        x.asIdeal • (⊤ : Submodule B (stalk B x (T1 d M)))) :
    (v : Fin 2 → K) ∈ (loc₀ d hle x).1.1 := by
  classical
  have hdx := hd x.asIdeal x.isPrime
  by_cases h0 : x ∈ S0 d (M := M) hle <;> by_cases h1 : x ∈ S1 d hπ hπM
  ·
    revert v hv
    rw [loc₀_eq_of_mem d hle h0, loc₁_eq_of_mem d hπ hπM h1]
    intro v hv
    have hv' := (sup_le (range_map_le_smul_top (Pi0 d hle) x h0) le_rfl) hv
    have hmem := one_tmul_mem_sup_of_stalkQuot_mem d x M v hv'
    by_contra h
    exact hdx.2.2.1 v h hmem
  ·
    revert v hv
    rw [loc₀_eq_of_mem d hle h0, loc₁_eq_of_not_mem d hπ hπM h1]
    intro v hv
    have hv' := (sup_le (range_map_le_smul_top (Pi0 d hle) x h0) le_rfl) hv
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe] at hv'
    have hv'' : stalkQuot x M' (d.line M') (sPi hπ M' x ((1 : locRing B x) ⊗ₜ[𝒪] v)) ∈
        x.asIdeal • (⊤ : Submodule B (stalk B x (T0 d M'))) := by
      have := Submodule.mem_map_of_mem
        (f := (LocalizedModule.map x.asIdeal.primeCompl (Pi1 d hπ hπM)).restrictScalars B) hv'
      rw [Submodule.map_smul'', Submodule.map_top] at this
      have := Submodule.smul_mono (le_refl x.asIdeal) (le_top (a := LinearMap.range _)) this
      rwa [LinearMap.restrictScalars_apply, map_Pi1_Pi1inv] at this
    rw [sPi, LinearMap.baseChange_tmul] at hv''
    have hmem := one_tmul_mem_sup_of_stalkQuot_mem d x M' _ hv''

    have hvM : (v : Fin 2 → K) ∈ M.1 := by
      by_contra hvM
      refine hdx.2.2.2 (smulInto π (smul_mem_of_mem_Mpi (K := K) hπ M') v) ?_ hmem
      rintro ⟨w, hw⟩
      rw [coe_smulInto_apply] at hw
      have hvw := smul_right_injective _ (hπK_of_irreducible (K := K) hπ) hw
      exact hvM (hvw ▸ w.2)

    by_contra hvM'
    have h3 := hdx.2.2.1 ⟨v, hvM⟩ hvM'
    have h5 := not_mem_sup_smul_of_not_mem_S1 d hπ hπM x h1 _ h3
    rw [LinearMap.baseChange_tmul] at h5
    have he : smulInto π hπM ⟨(v : Fin 2 → K), hvM⟩ = smulInto π (smul_mem_of_mem_Mpi (K := K) hπ M') v :=
      Subtype.ext rfl
    rw [he] at h5
    exact h5 hmem
  ·
    revert v hv
    rw [loc₀_eq_of_not_mem d hle h0, loc₁_eq_of_mem d hπ hπM h1]
    intro v _
    exact v.2
  · exact ((mem_S0_or_mem_S1 d hπ hle hπM hB x).elim h0 h1).elim

private theorem _root_.X2Body.hasDetIndex₀_loc (hπ : Irreducible π) (hle : M'.1 ≤ M.1) (hπM : ∀ v ∈ M.1, algebraMap 𝒪 K π • v ∈ M'.1)
    (h0 : HasDetIndex π M'.1 0) (hd : d.InEdgeChart π M' M) (x : PrimeSpectrum B)
    (hx : LinearMap.range (Pi0 d hle) ≤ x.asIdeal • (⊤ : Submodule B (T1 d M))) :
    HasDetIndex π (loc₀ d hle x).1.1 0 := by
  exact B25X2.hasDetIndex₀_loc d hπ hle hπM h0 hd x hx

p2m_export "X2Body" "hasDetIndex₀_loc"

private theorem _root_.X2Body.hasDetIndex₁_loc (hπ : Irreducible π) (hle : M'.1 ≤ M.1) (hπM : ∀ v ∈ M.1, algebraMap 𝒪 K π • v ∈ M'.1)
    (hB : IsNilpotent (algebraMap 𝒪 B π)) (h0 : HasDetIndex π M'.1 0) (hd : d.InEdgeChart π M' M)
    (hMM : M'.1 ≠ M.1) (x : PrimeSpectrum B)
    (hx : LinearMap.range (Pi1 d hπ hπM) ≤ x.asIdeal • (⊤ : Submodule B (T0 d M'))) :
    HasDetIndex π (loc₁ d hπ hπM x).1.1 (-1) := by
  exact B25X2.hasDetIndex₁_loc d hπ hle hπM hB h0 hd hMM x hx

p2m_export "X2Body" "hasDetIndex₁_loc"
end Local2

end X2Body
p2m_reactivate "P2MW.S_CerednikDrinfeld_FormalOmega_DeligneDatum_exists_isQuadrupleOf_and_pi_eq_smul_chartERing_of_line_eq.X2Body"

namespace X2E

open X2Body

section Rec

variable {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K]
  [IsFractionRing 𝒪 K] {π : 𝒪}
variable {B : Type} [CommRing B] [Algebra 𝒪 B]

noncomputable def X2rec (hπ : Irreducible π) (hB : IsNilpotent (algebraMap 𝒪 B π))
    {M' M : FullLattice 𝒪 K} (hle : M'.1 ≤ M.1) (hπM : ∀ v ∈ M.1, algebraMap 𝒪 K π • v ∈ M'.1)
    (h0 : HasDetIndex π M'.1 0)
    (d : DeligneDatum (K := K) π B) (hd : d.InEdgeChart π M' M) (hMM : M'.1 ≠ M.1) :
    DrinfeldDatum (K := K) π B := by
  classical
  exact {
    N₀ := fun x => (loc₀ d hle x).1.1
    N₁ := fun x => (loc₁ d hπ hπM x).1.1
    full₀ := fun x => (loc₀ d hle x).1.2
    full₁ := fun x => (loc₁ d hπ hπM x).1.2
    le := fun x => loc_le d hπ hle hπM x
    smul_le := fun x => loc_smul_le d hπ hle hπM x
    isOpen_setOf_mem₀ := fun v => isOpen_setOf_mem_loc₀ d hle v
    isOpen_setOf_mem₁ := fun v => isOpen_setOf_mem_loc₁ d hπ hle hπM v
    T₀ := T0 d M'
    T₁ := T1 d M
    invertible₀ := inferInstance
    invertible₁ := inferInstance
    Pi₀ := Pi0 d hle
    Pi₁ := Pi1 d hπ hπM
    Pi₁_Pi₀ := Pi1_Pi0 d hπ hle hπM
    Pi₀_Pi₁ := Pi0_Pi1 d hπ hle hπM
    u₀ := fun x => (loc₀ d hle x).2
    u₁ := fun x => (loc₁ d hπ hπM x).2
    u₁_incl := fun x w => u₁_incl_loc d hπ hle hπM x (loc_le d hπ hle hπM x) w
    u₀_smul := fun x w => u₀_smul_loc d hπ hle hπM x (loc_smul_le d hπ hle hπM x) w
    u₀_surjective := fun x => loc₀_surjective d hle x
    u₁_surjective := fun x => loc₁_surjective d hπ hπM x
    u₀_continuous := fun x v hvx => u₀_continuous_loc d hle x v hvx
    u₁_continuous := fun x v hvx => u₁_continuous_loc d hπ hle hπM x v hvx
    locallyConstant₀ := fun x hx => locallyConstant_loc₀ d hle x hx
    locallyConstant₁ := fun x hx => locallyConstant_loc₁ d hπ hπM x hx
    injective₀ := fun x v hv => injective₀_loc d hπ hle hπM hB hd x v hv
    injective₁ := fun x v hv => injective₁_loc d hπ hle hπM hB hd x v hv
    hasDetIndex₀ := fun x hx => hasDetIndex₀_loc d hπ hle hπM h0 hd x hx
    hasDetIndex₁ := fun x hx => hasDetIndex₁_loc d hπ hle hπM hB h0 hd hMM x hx }

theorem X2rec_isQuadrupleOf (hπ : Irreducible π) (hB : IsNilpotent (algebraMap 𝒪 B π))
    {M' M : FullLattice 𝒪 K} (hle : M'.1 ≤ M.1) (hπM : ∀ v ∈ M.1, algebraMap 𝒪 K π • v ∈ M'.1)
    (h0 : HasDetIndex π M'.1 0)
    (d : DeligneDatum (K := K) π B) (hd : d.InEdgeChart π M' M) (hMM : M'.1 ≠ M.1) :
    (X2rec hπ hB hle hπM h0 d hd hMM).IsQuadrupleOf d := by
  classical
  intro x
  exact ⟨edgeNondegAt_loc d hπ hle hπM hB hd x, ker_loc₀ d hle x, ker_loc₁ d hπ hπM x⟩

theorem X2rec_T₀ (hπ : Irreducible π) (hB : IsNilpotent (algebraMap 𝒪 B π))
    {M' M : FullLattice 𝒪 K} (hle : M'.1 ≤ M.1) (hπM : ∀ v ∈ M.1, algebraMap 𝒪 K π • v ∈ M'.1)
    (h0 : HasDetIndex π M'.1 0)
    (d : DeligneDatum (K := K) π B) (hd : d.InEdgeChart π M' M) (hMM : M'.1 ≠ M.1) :
    (X2rec hπ hB hle hπM h0 d hd hMM).T₀ = T0 d M' := rfl

end Rec
p2m_reactivate "P2MW.S_CerednikDrinfeld_FormalOmega_DeligneDatum_exists_isQuadrupleOf_and_pi_eq_smul_chartERing_of_line_eq.X2Body"

section Gen

variable {B : Type} [CommRing B] {V : Type} [AddCommGroup V] [Module B V]

theorem quot_line_gen (β : Module.Basis (Fin 2) B V) (c : B) (N : Submodule B V)
    (hN : N = Submodule.span B {c • β 0 + β 1}) :
    (∀ t : V ⧸ N, ∃! r : B, t = r • N.mkQ (β 0)) ∧ N.mkQ (β 1) = (-c) • N.mkQ (β 0) := by
  classical

  let f : V →ₗ[B] B :=
    (Finsupp.lapply 0).comp β.repr.toLinearMap - c • ((Finsupp.lapply 1).comp β.repr.toLinearMap)
  have hfapply : ∀ v, f v = β.repr v 0 - c * β.repr v 1 := fun v => by
    simp [f, smul_eq_mul]
  have hf0 : f (β 0) = 1 := by
    rw [hfapply, Module.Basis.repr_self]; simp [Finsupp.single_apply]
  have hf1 : f (β 1) = -c := by
    rw [hfapply, Module.Basis.repr_self]; simp [Finsupp.single_apply]
  have hfN : N ≤ LinearMap.ker f := by
    rw [hN, Submodule.span_le]
    intro v hv
    rw [Set.mem_singleton_iff] at hv
    subst hv
    rw [SetLike.mem_coe, LinearMap.mem_ker, map_add, map_smul, hf0, hf1, smul_eq_mul, mul_one, add_neg_cancel]
  have hmem : c • β 0 + β 1 ∈ N := by rw [hN]; exact Submodule.subset_span (Set.mem_singleton _)
  have hrel : N.mkQ (β 1) = (-c) • N.mkQ (β 0) := by
    rw [neg_smul, eq_neg_iff_add_eq_zero, add_comm, ← map_smul, ← map_add, Submodule.mkQ_apply,
      Submodule.Quotient.mk_eq_zero]
    exact hmem
  refine ⟨fun t => ?_, hrel⟩
  obtain ⟨v, rfl⟩ := Submodule.mkQ_surjective N t
  refine ⟨f v, ?_, ?_⟩
  ·
    have hv := β.sum_repr v
    rw [Fin.sum_univ_two] at hv
    rw [hfapply]
    calc N.mkQ v = N.mkQ (β.repr v 0 • β 0 + β.repr v 1 • β 1) := by rw [hv]
      _ = (β.repr v 0 - c * β.repr v 1) • N.mkQ (β 0) := by
        rw [map_add, map_smul, map_smul, hrel, smul_smul, ← add_smul]
        congr 1
        ring
  · intro r hr
    have := congrArg (N.liftQ f hfN) hr
    rw [map_smul, Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.liftQ_apply, Submodule.liftQ_apply, hf0,
      smul_eq_mul, mul_one] at this
    exact this.symm

end Gen
p2m_reactivate "P2MW.S_CerednikDrinfeld_FormalOmega_DeligneDatum_exists_isQuadrupleOf_and_pi_eq_smul_chartERing_of_line_eq.X2Body"

section Std

variable {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] {K : Type} [Field K] [Algebra 𝒪 K] [IsFractionRing 𝒪 K]

theorem coe_stdBasisVec (i : Fin 2) :
    ((stdBasisVec (𝒪 := 𝒪) K i : ↥(stdFullLattice (𝒪 := 𝒪) K).1) : Fin 2 → K) = Pi.single i 1 := rfl

theorem linearIndependent_stdBasisVec : LinearIndependent 𝒪 (stdBasisVec (𝒪 := 𝒪) K) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have h := congrArg Subtype.val hg
  rw [Fin.sum_univ_two, Submodule.coe_add, Submodule.coe_smul, Submodule.coe_smul, coe_stdBasisVec,
    coe_stdBasisVec, Submodule.coe_zero] at h
  have h0 : algebraMap 𝒪 K (g 0) = 0 := by
    simpa [Pi.single_apply, Algebra.smul_def] using congrFun h 0
  have h1 : algebraMap 𝒪 K (g 1) = 0 := by
    simpa [Pi.single_apply, Algebra.smul_def] using congrFun h 1
  intro i
  fin_cases i
  · exact (IsFractionRing.injective 𝒪 K) (by simpa using h0)
  · exact (IsFractionRing.injective 𝒪 K) (by simpa using h1)

theorem span_stdBasisVec : Submodule.span 𝒪 (Set.range (stdBasisVec (𝒪 := 𝒪) K)) = ⊤ := by
  apply Submodule.map_injective_of_injective (stdFullLattice (𝒪 := 𝒪) K).1.injective_subtype
  rw [Submodule.map_top, Submodule.range_subtype, Submodule.map_span, ← Set.range_comp]
  show Submodule.span 𝒪 (Set.range fun j => (Pi.single j 1 : Fin 2 → K)) = stdLattice 𝒪 K
  exact (stdLattice_eq_span 𝒪 K).symm

noncomputable def stdB : Module.Basis (Fin 2) 𝒪 ↥(stdFullLattice (𝒪 := 𝒪) K).1 :=
  Module.Basis.mk (linearIndependent_stdBasisVec (K := K)) (span_stdBasisVec (K := K)).ge

@[scoped simp] theorem stdB_apply (i : Fin 2) : stdB (𝒪 := 𝒪) (K := K) i = stdBasisVec K i :=
  Module.Basis.mk_apply _ _ i

end Std
p2m_reactivate "P2MW.S_CerednikDrinfeld_FormalOmega_DeligneDatum_exists_isQuadrupleOf_and_pi_eq_smul_chartERing_of_line_eq.X2Body"

section Main

open scoped Matrix

variable {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K]
  [IsFractionRing 𝒪 K]

theorem memStd (v : Fin 2 → K) :
    v ∈ (stdFullLattice (𝒪 := 𝒪) K).1 ↔ ∀ i, IsLocalization.IsInteger 𝒪 (v i) := Iff.rfl

theorem hasDetIndex_std (π : 𝒪) : HasDetIndex π (stdFullLattice (𝒪 := 𝒪) K).1 0 := by
  refine ⟨1, latticeMap_one _, 1, ?_⟩
  simp

variable {π : 𝒪} (hπ : Irreducible π)
variable (g : Matrix.GeneralLinearGroup (Fin 2) K)
  (hg : (g : Matrix (Fin 2) (Fin 2) K) = Matrix.diagonal ![algebraMap 𝒪 K π, 1])

noncomputable abbrev Mbig : FullLattice 𝒪 K :=
  FullLattice.act (scalarGL (piUnit (K := K) hπ)⁻¹) (FullLattice.act g (stdFullLattice K))

theorem coe_piUnit : ((piUnit (K := K) hπ : Kˣ) : K) = algebraMap 𝒪 K π := rfl

include hg in
theorem g_mulVec (v : Fin 2 → K) :
    (g : Matrix (Fin 2) (Fin 2) K) *ᵥ v = ![algebraMap 𝒪 K π * v 0, v 1] := by
  rw [hg]; funext i; rw [Matrix.mulVec_diagonal]; fin_cases i <;> simp

include hg in
theorem hle : (stdFullLattice (𝒪 := 𝒪) K).1 ≤ (Mbig hπ g).1 := by
  intro v hv
  rw [memStd] at hv
  refine mem_latticeMap_scalarGL.mpr ⟨(piUnit (K := K) hπ : K) • v, ?_, ?_⟩
  · refine mem_latticeMap.mpr ⟨![v 0, algebraMap 𝒪 K π * v 1], ?_, ?_⟩
    · rw [memStd]; intro i; fin_cases i
      · simpa using hv 0
      · simpa using IsLocalization.isInteger_mul ⟨π, rfl⟩ (hv 1)
    · rw [g_mulVec g hg, coe_piUnit]; funext i; fin_cases i <;> simp
  · rw [smul_smul, Units.inv_mul, one_smul]

include hg in
theorem hπM : ∀ v ∈ (Mbig hπ g).1, algebraMap 𝒪 K π • v ∈ (stdFullLattice (𝒪 := 𝒪) K).1 := by
  intro v hv
  obtain ⟨w, hw, rfl⟩ := mem_latticeMap_scalarGL.mp hv
  obtain ⟨u, hu, rfl⟩ := mem_latticeMap.mp hw
  rw [memStd] at hu
  rw [← coe_piUnit hπ, smul_smul, Units.mul_inv, one_smul, g_mulVec g hg, memStd]
  intro i; fin_cases i
  · simpa using IsLocalization.isInteger_mul ⟨π, rfl⟩ (hu 0)
  · simpa using hu 1

include hg in
theorem hMM : (stdFullLattice (𝒪 := 𝒪) K).1 ≠ (Mbig hπ g).1 := by
  intro h
  have hmem : (((piUnit (K := K) hπ)⁻¹ : Kˣ) : K) • (Pi.single 1 1 : Fin 2 → K) ∈ (Mbig hπ g).1 := by
    refine mem_latticeMap_scalarGL.mpr ⟨Pi.single 1 1, ?_, rfl⟩
    refine mem_latticeMap.mpr ⟨Pi.single 1 1, single_one_mem_stdLattice 𝒪 K 1, ?_⟩
    rw [g_mulVec g hg]; funext i; fin_cases i <;> simp
  rw [← h, memStd] at hmem
  obtain ⟨r, hr⟩ := hmem 1
  simp only [Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one] at hr
  apply hπ.not_isUnit
  refine IsUnit.of_mul_eq_one r ((IsFractionRing.injective 𝒪 K) ?_)
  rw [map_mul, hr, map_one, ← coe_piUnit hπ, Units.mul_inv]

noncomputable def mEquiv : ↥(stdFullLattice (𝒪 := 𝒪) K).1 ≃ₗ[𝒪] ↥(Mbig hπ g).1 :=
  (latticeMapEquiv g (stdFullLattice (𝒪 := 𝒪) K).1).trans
    (latticeMapEquiv (scalarGL (piUnit (K := K) hπ)⁻¹) (FullLattice.act g (stdFullLattice K)).1)

theorem coe_mEquiv (v : ↥(stdFullLattice (𝒪 := 𝒪) K).1) :
    ((mEquiv hπ g v : ↥(Mbig hπ g).1) : Fin 2 → K) =
      (((piUnit (K := K) hπ)⁻¹ : Kˣ) : K) • ((g : Matrix (Fin 2) (Fin 2) K) *ᵥ (v : Fin 2 → K)) := by
  change ((scalarGL ((piUnit (K := K) hπ)⁻¹) : Matrix.GeneralLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *ᵥ
      ((g : Matrix (Fin 2) (Fin 2) K) *ᵥ (v : Fin 2 → K)) = _
  rw [scalarGL_mulVec]

include hg in
theorem coe_mEquiv_zero : ((mEquiv hπ g (stdBasisVec K 0) : ↥(Mbig hπ g).1) : Fin 2 → K) = Pi.single 0 1 := by
  rw [coe_mEquiv, coe_stdBasisVec, g_mulVec g hg]
  funext i; fin_cases i
  · simp [Units.val_inv_eq_inv_val, coe_piUnit hπ, hπK_of_irreducible (K := K) hπ]
  · simp

include hg in
theorem coe_mEquiv_one :
    ((mEquiv hπ g (stdBasisVec K 1) : ↥(Mbig hπ g).1) : Fin 2 → K) =
      (((piUnit (K := K) hπ)⁻¹ : Kˣ) : K) • Pi.single 1 1 := by
  rw [coe_mEquiv, coe_stdBasisVec, g_mulVec g hg]
  congr 1; funext i; fin_cases i <;> simp

include hg in

theorem inclusion_e0 :
    Submodule.inclusion (hle hπ g hg) (stdBasisVec K 0) = mEquiv hπ g (stdBasisVec K 0) :=
  Subtype.ext (by rw [Submodule.coe_inclusion, coe_mEquiv_zero hπ g hg, coe_stdBasisVec])

include hg in

theorem smulInto_mEquiv_e1 :
    smulInto π (hπM hπ g hg) (mEquiv hπ g (stdBasisVec K 1)) = stdBasisVec K 1 :=
  Subtype.ext (by
    rw [coe_smulInto_apply, coe_mEquiv_one hπ g hg, coe_stdBasisVec, smul_smul, ← coe_piUnit hπ, Units.mul_inv,
      one_smul])

variable {B : Type} [CommRing B] [Algebra 𝒪 B]

noncomputable def βstd : Module.Basis (Fin 2) B (latticeBaseChange 𝒪 K B (stdFullLattice K)) :=
  Algebra.TensorProduct.basis B (stdB (𝒪 := 𝒪) (K := K))

theorem βstd_apply (i : Fin 2) : βstd (B := B) (𝒪 := 𝒪) (K := K) i = (1 : B) ⊗ₜ[𝒪] stdBasisVec K i := by
  rw [βstd, Algebra.TensorProduct.basis_apply, stdB_apply]

noncomputable def βM : Module.Basis (Fin 2) B (latticeBaseChange 𝒪 K B (Mbig hπ g)) :=
  Algebra.TensorProduct.basis B ((stdB (𝒪 := 𝒪) (K := K)).map (mEquiv hπ g))

theorem βM_apply (i : Fin 2) : βM (B := B) hπ g i = (1 : B) ⊗ₜ[𝒪] mEquiv hπ g (stdBasisVec K i) := by
  rw [βM, Algebra.TensorProduct.basis_apply, Module.Basis.map_apply, stdB_apply]

theorem actBaseChange_actBaseChange_tmul (b : B) (v : ↥(stdFullLattice (𝒪 := 𝒪) K).1) :
    actBaseChange B (scalarGL (piUnit (K := K) hπ)⁻¹) (FullLattice.act g (stdFullLattice K))
        (actBaseChange B g (stdFullLattice K) (b ⊗ₜ[𝒪] v)) = b ⊗ₜ[𝒪] mEquiv hπ g v := by
  rfl

end Main
p2m_reactivate "P2MW.S_CerednikDrinfeld_FormalOmega_DeligneDatum_exists_isQuadrupleOf_and_pi_eq_smul_chartERing_of_line_eq.X2Body"

end X2E
p2m_reactivate "P2MW.S_CerednikDrinfeld_FormalOmega_DeligneDatum_exists_isQuadrupleOf_and_pi_eq_smul_chartERing_of_line_eq.X2Body P2MW.S_CerednikDrinfeld_FormalOmega_DeligneDatum_exists_isQuadrupleOf_and_pi_eq_smul_chartERing_of_line_eq.X2E"

open X2E X2Body in
theorem solution
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K] [IsFractionRing 𝒪 K]
    (π : 𝒪) (hπ : Irreducible π) (q : ℕ) (hq : Nat.card (𝒪 ⧸ Ideal.span {π}) = q) [Finite (𝒪 ⧸ Ideal.span {π})]
    (g : Matrix.GeneralLinearGroup (Fin 2) K) (hg : (g : Matrix (Fin 2) (Fin 2) K) = Matrix.diagonal ![algebraMap 𝒪 K π, 1])
    {B : Type} [CommRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π))
    (d : DeligneDatum (K := K) π B) (hd : d.InEdgeChart π (FullLattice.act g (stdFullLattice K)) (stdFullLattice K))
    (x : chartERing 𝒪 π q →ₐ[𝒪] B)
    (hx0 : d.line (stdFullLattice K) =
      Submodule.span B {(x (chartERing.ξ 𝒪 π q)) ⊗ₜ[𝒪] stdBasisVec K 0 + (1 : B) ⊗ₜ[𝒪] stdBasisVec K 1})
    (hx1 : d.line (FullLattice.act g (stdFullLattice K)) =
      (Submodule.span B {(1 : B) ⊗ₜ[𝒪] stdBasisVec K 0 + (x (chartERing.η 𝒪 π q)) ⊗ₜ[𝒪] stdBasisVec K 1}).map
        (actBaseChange B g (stdFullLattice K)).toLinearMap)
 :
    ∃ Q : DrinfeldDatum (K := K) π B, Q.IsQuadrupleOf d ∧
      ∃ (e₀ : Q.T₀) (e₁ : Q.T₁), (∀ t : Q.T₀, ∃! b : B, t = b • e₀) ∧ (∀ t : Q.T₁, ∃! b : B, t = b • e₁) ∧
        Q.Pi₀ e₀ = (-(x (chartERing.η 𝒪 π q))) • e₁ ∧ Q.Pi₁ e₁ = (-(x (chartERing.ξ 𝒪 π q))) • e₀ := by
  classical

  have hd' : d.InEdgeChart π (stdFullLattice K) (Mbig hπ g) :=
    DeligneDatum.inEdgeChart_act_scalarGL_inv_of_inEdgeChart π hπ (piUnit (K := K) hπ) (coe_piUnit hπ) d
      (FullLattice.act g (stdFullLattice K)) (stdFullLattice K) hd

  have hN0 : d.line (stdFullLattice K) =
      Submodule.span B {x (chartERing.ξ 𝒪 π q) • βstd (B := B) (𝒪 := 𝒪) (K := K) 0 + βstd 1} := by
    rw [hx0, βstd_apply, βstd_apply, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  have hN1 : d.line (Mbig hπ g) =
      Submodule.span B {x (chartERing.η 𝒪 π q) • (βM (B := B) hπ g).reindex (Equiv.swap 0 1) 0 +
        (βM (B := B) hπ g).reindex (Equiv.swap 0 1) 1} := by
    rw [Module.Basis.reindex_apply, Module.Basis.reindex_apply, Equiv.symm_swap, Equiv.swap_apply_left,
      Equiv.swap_apply_right, βM_apply, βM_apply]
    show d.line (FullLattice.act (scalarGL (piUnit (K := K) hπ)⁻¹) (FullLattice.act g (stdFullLattice K))) = _
    rw [d.homothety, hx1, ← Submodule.map_comp, Submodule.map_span, Set.image_singleton, LinearMap.comp_apply,
      LinearEquiv.coe_coe, LinearEquiv.coe_coe, map_add, map_add, actBaseChange_actBaseChange_tmul,
      ← mul_one (x (chartERing.η 𝒪 π q)), ← smul_eq_mul, ← TensorProduct.smul_tmul', map_smul, map_smul,
      actBaseChange_actBaseChange_tmul, smul_eq_mul, mul_one, add_comm]
  obtain ⟨hgen0, hrel0⟩ :=
    quot_line_gen (βstd (B := B) (𝒪 := 𝒪) (K := K)) (x (chartERing.ξ 𝒪 π q)) (d.line (stdFullLattice K)) hN0
  obtain ⟨hgen1, hrel1⟩ :=
    quot_line_gen ((βM (B := B) hπ g).reindex (Equiv.swap 0 1)) (x (chartERing.η 𝒪 π q)) (d.line (Mbig hπ g)) hN1
  simp only [Module.Basis.reindex_apply, Equiv.symm_swap, Equiv.swap_apply_left, Equiv.swap_apply_right] at hgen1 hrel1
  refine ⟨X2rec hπ hB (hle hπ g hg) (hπM hπ g hg) (hasDetIndex_std (K := K) π) d hd' (hMM hπ g hg),
    X2rec_isQuadrupleOf hπ hB _ _ _ d hd' _,
    (d.line (stdFullLattice K)).mkQ (βstd 0), (d.line (Mbig hπ g)).mkQ (βM hπ g 1), hgen0, hgen1, ?_, ?_⟩
  ·
    show Pi0 d (hle hπ g hg) ((d.line (stdFullLattice K)).mkQ (βstd 0)) =
      (-(x (chartERing.η 𝒪 π q))) • (d.line (Mbig hπ g)).mkQ (βM hπ g 1)
    rw [← hrel1, Pi0, Submodule.mkQ_apply, Submodule.mapQ_apply, βstd_apply, βM_apply, inclBaseChange,
      LinearMap.baseChange_tmul, inclusion_e0 hπ g hg]
    rfl
  ·
    show Pi1 d hπ (hπM hπ g hg) ((d.line (Mbig hπ g)).mkQ (βM hπ g 1)) =
      (-(x (chartERing.ξ 𝒪 π q))) • (d.line (stdFullLattice K)).mkQ (βstd 0)
    rw [← hrel0, Pi1, Submodule.mkQ_apply, Submodule.mapQ_apply, βstd_apply, βM_apply, LinearMap.baseChange_tmul,
      smulInto_mEquiv_e1 hπ g hg]
    rfl

end S_CerednikDrinfeld_FormalOmega_DeligneDatum_exists_isQuadrupleOf_and_pi_eq_smul_chartERing_of_line_eq
end P2MW
export P2MW.S_CerednikDrinfeld_FormalOmega_DeligneDatum_exists_isQuadrupleOf_and_pi_eq_smul_chartERing_of_line_eq (solution)
