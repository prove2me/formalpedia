-- Prove2me | solution 1 for CuspForm.exists_reductionModule_of_isLatticeRealized
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/a0ffe47e-9e40-5d32-a7f5-0e725ad0c27e

import Mathlib
import Definitions.Def_CuspForm_HeckeAlgebra
import Definitions.Def_CuspForm_IntegralStructure
import Definitions.Def_CuspForm_IntegralLattice
import Definitions.Def_PowerSeries_FormalHeckeOperators
import Theorems.Thm_CuspForm_mem_intLattice_of_mem_heckeAlgebra
import Theorems.Thm_CuspForm_mem_intLattice_iff
import Theorems.Thm_ModularFormClass_qCoeff_heckeT
import Theorems.Thm_CongruenceSubgroup_one_mem_strictPeriods_Gamma0
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CuspForm_exists_reductionModule_of_isLatticeRealized

set_option autoImplicit false

noncomputable section

open ModularForm ModularFormClass

namespace CuspForm
p2m_export "CuspForm" "IsGLPos.coe_smul mk coe_zero ext coe_smul coe_add heckeAlgebra heckeAlgebra.T heckeAlgebra.coe_T coe_heckeTLin_apply intLattice HasIntegralStructure IsLatticeRealized mem_intLattice_of_mem_heckeAlgebra mem_intLattice_iff"
namespace S17C
p2m_open "CuspForm"

local notation "Γ₀(" N ")" => CongruenceSubgroup.Gamma0 N

theorem hΓ (N : ℕ) :
    (1 : ℝ) ∈ (Subgroup.map (Matrix.SpecialLinearGroup.mapGL ℝ) Γ₀(N)).strictPeriods :=
  CongruenceSubgroup.one_mem_strictPeriods_Gamma0 N

variable {N : ℕ} {k : ℤ}

theorem qCoeff_add (f g : CuspForm Γ₀(N) k) (n : ℕ) :
    qCoeff ⇑(f + g) n = qCoeff ⇑f n + qCoeff ⇑g n := by
  have hf := ModularFormClass.analyticAt_cuspFunction_zero f one_pos (hΓ N)
  have hg := ModularFormClass.analyticAt_cuspFunction_zero g one_pos (hΓ N)
  simp only [qCoeff, CuspForm.coe_add]
  first
  | rw [UpperHalfPlane.qExpansion_add hf hg, map_add]
  | rw [ModularForm.qExpansion_add one_pos (hΓ N) f g, map_add]

theorem qCoeff_zero' (n : ℕ) : qCoeff ⇑(0 : CuspForm Γ₀(N) k) n = 0 := by
  simp only [qCoeff, CuspForm.coe_zero]
  rw [UpperHalfPlane.qExpansion_zero, map_zero]

theorem qCoeff_smul (c : ℂ) (f : CuspForm Γ₀(N) k) (n : ℕ) :
    qCoeff ⇑(c • f) n = c * qCoeff ⇑f n := by
  have hf := ModularFormClass.analyticAt_cuspFunction_zero f one_pos (hΓ N)
  simp only [qCoeff, CuspForm.IsGLPos.coe_smul]
  first
  | rw [UpperHalfPlane.qExpansion_smul hf, map_smul, smul_eq_mul]
  | (rw [← CuspForm.IsGLPos.coe_smul, ModularForm.qExpansion_smul one_pos (hΓ N) c f]; simp)

theorem qCoeff_zsmul (c : ℤ) (f : CuspForm Γ₀(N) k) (n : ℕ) :
    qCoeff ⇑(c • f) n = c * qCoeff ⇑f n := by
  rw [← Int.cast_smul_eq_zsmul ℂ c f, qCoeff_smul]

abbrev Lat (N : ℕ) : Submodule ℤ (CuspForm Γ₀(N) 2) := CuspForm.intLattice N 2

theorem exists_intCast_of_mem {f : CuspForm Γ₀(N) 2} (hf : f ∈ Lat N) (n : ℕ) :
    ∃ m : ℤ, qCoeff ⇑f n = (m : ℂ) :=
  (CuspForm.mem_intLattice_iff f).mp hf n

def intQExpansion (f : Lat N) : PowerSeries ℤ :=
  PowerSeries.mk fun n => (exists_intCast_of_mem f.2 n).choose

theorem intQExpansion_cast (f : Lat N) (n : ℕ) :
    ((PowerSeries.coeff n (intQExpansion f) : ℤ) : ℂ) = qCoeff ⇑(f : CuspForm Γ₀(N) 2) n := by
  simp only [intQExpansion, PowerSeries.coeff_mk]
  exact (exists_intCast_of_mem f.2 n).choose_spec.symm

theorem intQExpansion_zero : intQExpansion (0 : Lat N) = 0 := by
  ext n
  have h0 : ((PowerSeries.coeff n (intQExpansion (0 : Lat N)) : ℤ) : ℂ) = 0 := by
    rw [intQExpansion_cast]
    exact qCoeff_zero' n
  have : PowerSeries.coeff n (intQExpansion (0 : Lat N)) = 0 := by exact_mod_cast h0
  simpa using this

theorem intQExpansion_add (f g : Lat N) :
    intQExpansion (f + g) = intQExpansion f + intQExpansion g := by
  ext n
  have h : ((PowerSeries.coeff n (intQExpansion (f + g)) : ℤ) : ℂ)
      = ((PowerSeries.coeff n (intQExpansion f) + PowerSeries.coeff n (intQExpansion g) : ℤ) : ℂ) := by
    rw [intQExpansion_cast]
    push_cast
    rw [intQExpansion_cast, intQExpansion_cast]
    exact qCoeff_add (f : CuspForm Γ₀(N) 2) (g : CuspForm Γ₀(N) 2) n
  have h' := Int.cast_injective (α := ℂ) h
  simpa using h'

theorem intQExpansion_sub (f g : Lat N) :
    intQExpansion (f - g) = intQExpansion f - intQExpansion g := by
  have hadd := intQExpansion_add (f - g) g
  rw [sub_add_cancel] at hadd
  exact eq_sub_of_add_eq hadd.symm

theorem coeff_intQExpansion_zsmul (c : ℤ) (f : Lat N) (n : ℕ) :
    PowerSeries.coeff n (intQExpansion (c • f)) = c * PowerSeries.coeff n (intQExpansion f) := by
  have h : ((PowerSeries.coeff n (intQExpansion (c • f)) : ℤ) : ℂ)
      = ((c * PowerSeries.coeff n (intQExpansion f) : ℤ) : ℂ) := by
    rw [intQExpansion_cast, Submodule.coe_smul, qCoeff_zsmul]
    push_cast
    rw [intQExpansion_cast]
  exact Int.cast_injective (α := ℂ) h

def threeMultiples (N : ℕ) : Submodule ℤ (Lat N) :=
  LinearMap.range ((3 : ℤ) • (LinearMap.id : Lat N →ₗ[ℤ] Lat N))

theorem mem_threeMultiples_iff {f : Lat N} :
    f ∈ threeMultiples N ↔ ∃ g : Lat N, (3 : ℤ) • g = f := by
  constructor
  · rintro ⟨g, hg⟩
    exact ⟨g, hg⟩
  · rintro ⟨g, hg⟩
    exact ⟨g, hg⟩

theorem mem_threeMultiples_iff_dvd {f : Lat N} :
    f ∈ threeMultiples N ↔ ∀ n, (3 : ℤ) ∣ PowerSeries.coeff n (intQExpansion f) := by
  constructor
  · rintro hf n
    obtain ⟨g, rfl⟩ := mem_threeMultiples_iff.mp hf
    rw [coeff_intQExpansion_zsmul]
    exact dvd_mul_right 3 _
  · intro hdvd

    have hmem : (3⁻¹ : ℂ) • (f : CuspForm Γ₀(N) 2) ∈ Lat N := by
      rw [CuspForm.mem_intLattice_iff]
      intro n
      obtain ⟨m, hm⟩ := hdvd n
      refine ⟨m, ?_⟩
      have hcoeff := intQExpansion_cast f n
      rw [hm] at hcoeff
      push_cast at hcoeff
      rw [qCoeff_smul, ← hcoeff, ← mul_assoc, inv_mul_cancel₀ (by norm_num : (3 : ℂ) ≠ 0), one_mul]
    refine mem_threeMultiples_iff.mpr ⟨⟨(3⁻¹ : ℂ) • (f : CuspForm Γ₀(N) 2), hmem⟩, ?_⟩
    ext1
    show (3 : ℤ) • ((3⁻¹ : ℂ) • (f : CuspForm Γ₀(N) 2)) = (f : CuspForm Γ₀(N) 2)
    rw [← Int.cast_smul_eq_zsmul ℂ (3 : ℤ), smul_smul]
    norm_num

abbrev LatticeMod3 (N : ℕ) : Type := Lat N ⧸ threeMultiples N

abbrev latticeMk (f : Lat N) : LatticeMod3 N := Submodule.Quotient.mk f

theorem latticeMk_eq_zero_iff {f : Lat N} :
    latticeMk f = 0 ↔ ∀ n, (3 : ℤ) ∣ PowerSeries.coeff n (intQExpansion f) := by
  rw [Submodule.Quotient.mk_eq_zero]
  exact mem_threeMultiples_iff_dvd

theorem latticeMk_eq_of_dvd_sub {f g : Lat N}
    (h : ∀ n, (3 : ℤ) ∣ PowerSeries.coeff n (intQExpansion f) - PowerSeries.coeff n (intQExpansion g)) :
    latticeMk f = latticeMk g := by
  rw [Submodule.Quotient.eq, mem_threeMultiples_iff_dvd]
  intro n
  rw [intQExpansion_sub, map_sub]
  exact h n

section Action

variable [NeZero N]

abbrev HA (N : ℕ) [NeZero N] := CuspForm.heckeAlgebra N 2 {ℓ | ℓ ∣ N}

def latticeAction (T : HA N) : Lat N →ₗ[ℤ] Lat N :=
  ((T : Module.End ℂ (CuspForm Γ₀(N) 2)).restrictScalars ℤ).restrict
    fun f hf => CuspForm.mem_intLattice_of_mem_heckeAlgebra (by norm_num) T.2 hf

@[scoped simp] theorem latticeAction_apply_coe (T : HA N) (f : Lat N) :
    ((latticeAction T f : Lat N) : CuspForm Γ₀(N) 2)
      = (T : Module.End ℂ (CuspForm Γ₀(N) 2)) (f : CuspForm Γ₀(N) 2) :=
  rfl

theorem latticeAction_one : latticeAction (1 : HA N) = LinearMap.id := by
  refine LinearMap.ext fun f => Subtype.ext ?_
  rw [latticeAction_apply_coe]
  rfl

theorem latticeAction_mul (T S : HA N) :
    latticeAction (T * S) = latticeAction T ∘ₗ latticeAction S := by
  refine LinearMap.ext fun f => Subtype.ext ?_
  rw [latticeAction_apply_coe]
  rfl

theorem latticeAction_add (T S : HA N) :
    latticeAction (T + S) = latticeAction T + latticeAction S := by
  refine LinearMap.ext fun f => Subtype.ext ?_
  rw [latticeAction_apply_coe]
  rfl

theorem latticeAction_zero : latticeAction (0 : HA N) = 0 := by
  refine LinearMap.ext fun f => Subtype.ext ?_
  rw [latticeAction_apply_coe]
  rfl

theorem threeMultiples_le_comap_latticeAction (T : HA N) :
    threeMultiples N ≤ (threeMultiples N).comap (latticeAction T) := by
  rintro f hf
  obtain ⟨g, rfl⟩ := mem_threeMultiples_iff.mp hf
  exact mem_threeMultiples_iff.mpr ⟨latticeAction T g, (map_smul (latticeAction T) _ _).symm⟩

def heckeSMulAux (T : HA N) : LatticeMod3 N →ₗ[ℤ] LatticeMod3 N :=
  Submodule.mapQ (threeMultiples N) (threeMultiples N) (latticeAction T)
    (threeMultiples_le_comap_latticeAction T)

scoped instance : SMul (HA N) (LatticeMod3 N) := ⟨fun T m => heckeSMulAux T m⟩

theorem heckeSMul_def (T : HA N) (m : LatticeMod3 N) : T • m = heckeSMulAux T m := rfl

theorem heckeSMul_mk (T : HA N) (f : Lat N) : T • latticeMk f = latticeMk (latticeAction T f) := rfl

scoped instance : Module (HA N) (LatticeMod3 N) where
  one_smul m := by
    obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ m
    show (1 : HA N) • latticeMk f = latticeMk f
    rw [heckeSMul_mk, latticeAction_one]
    rfl
  mul_smul T S m := by
    obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ m
    show (T * S) • latticeMk f = T • S • latticeMk f
    rw [heckeSMul_mk, heckeSMul_mk, heckeSMul_mk, latticeAction_mul]
    rfl
  smul_zero T := map_zero (heckeSMulAux T)
  smul_add T m m' := map_add (heckeSMulAux T) m m'
  add_smul T S m := by
    obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ m
    show (T + S) • latticeMk f = T • latticeMk f + S • latticeMk f
    rw [heckeSMul_mk, heckeSMul_mk, heckeSMul_mk, latticeAction_add]
    rfl
  zero_smul m := by
    obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ m
    show (0 : HA N) • latticeMk f = 0
    rw [heckeSMul_mk, latticeAction_zero]
    rfl

theorem latticeAction_intCast (z : ℤ) (f : Lat N) : latticeAction (z : HA N) f = z • f := by
  apply Subtype.ext
  simp only [latticeAction_apply_coe, SubringClass.coe_intCast, Module.End.intCast_apply,
    Submodule.coe_smul]

theorem intCast_heckeSMul_mk (z : ℤ) (f : Lat N) :
    ((z : HA N)) • latticeMk f = latticeMk (z • f) := by
  rw [heckeSMul_mk, latticeAction_intCast]

end Action

open Classical in

def latticeReduction (m₀ : LatticeMod3 N) (g : PowerSeries ℤ) : LatticeMod3 N :=
  if h : ∃ f : Lat N, ∀ n, (3 : ℤ) ∣ PowerSeries.coeff n (intQExpansion f) - PowerSeries.coeff n g then
    latticeMk h.choose
  else m₀

theorem latticeReduction_eq_mk (m₀ : LatticeMod3 N) {g : PowerSeries ℤ} {f : Lat N}
    (hf : ∀ n, (3 : ℤ) ∣ PowerSeries.coeff n (intQExpansion f) - PowerSeries.coeff n g) :
    latticeReduction m₀ g = latticeMk f := by
  have hex : ∃ f' : Lat N, ∀ n, (3 : ℤ) ∣ PowerSeries.coeff n (intQExpansion f') - PowerSeries.coeff n g :=
    ⟨f, hf⟩
  rw [latticeReduction, dif_pos hex]
  refine latticeMk_eq_of_dvd_sub fun n => ?_
  have h1 := hex.choose_spec n
  have h2 := hf n
  have hsplit : PowerSeries.coeff n (intQExpansion hex.choose) - PowerSeries.coeff n (intQExpansion f)
      = (PowerSeries.coeff n (intQExpansion hex.choose) - PowerSeries.coeff n g)
        - (PowerSeries.coeff n (intQExpansion f) - PowerSeries.coeff n g) := by ring
  rw [hsplit]
  exact dvd_sub h1 h2

theorem latticeReduction_eq_zero (m₀ : LatticeMod3 N) {g : PowerSeries ℤ}
    (hg : ∀ n, (3 : ℤ) ∣ PowerSeries.coeff n g) : latticeReduction m₀ g = 0 := by
  have h0 : ∀ n, (3 : ℤ) ∣ PowerSeries.coeff n (intQExpansion (0 : Lat N)) - PowerSeries.coeff n g := by
    intro n
    rw [intQExpansion_zero]
    simp only [map_zero, zero_sub, dvd_neg]
    exact hg n
  rw [latticeReduction_eq_mk m₀ h0, latticeMk_eq_zero_iff]
  intro n
  rw [intQExpansion_zero]
  simp

theorem latticeReduction_dvd_of_eq_zero {m₀ : LatticeMod3 N} (hm₀ : m₀ ≠ 0) (g : PowerSeries ℤ)
    (hg : latticeReduction m₀ g = 0) : (3 : ℤ) ∣ PowerSeries.coeff 1 g := by
  by_cases hex : ∃ f : Lat N, ∀ n, (3 : ℤ) ∣ PowerSeries.coeff n (intQExpansion f) - PowerSeries.coeff n g
  · obtain ⟨f, hf⟩ := hex
    rw [latticeReduction_eq_mk m₀ hf, latticeMk_eq_zero_iff] at hg
    have h1 := hg 1
    have h2 := hf 1
    have hsplit : PowerSeries.coeff 1 g
        = PowerSeries.coeff 1 (intQExpansion f)
          - (PowerSeries.coeff 1 (intQExpansion f) - PowerSeries.coeff 1 g) := by ring
    rw [hsplit]
    exact dvd_sub h1 h2
  · rw [latticeReduction, dif_neg hex] at hg
    exact absurd hg hm₀

open EisensteinWeightOne in

theorem coeff_one_bridgeProduct (a : ℕ → ℤ) :
    PowerSeries.coeff 1 (bridgeProduct a) = a 1 + a 0 * (6 * sigmaChi 1) := by
  rw [bridgeProduct, PowerSeries.coeff_mul, Finset.Nat.antidiagonal_succ, Finset.sum_cons,
    Finset.Nat.antidiagonal_zero, Finset.map_singleton, Finset.sum_singleton]
  simp [e1Chi3In, e1Chi3, PowerSeries.coeff_mk]
  ring

theorem not_three_dvd_coeff_one_bridgeProduct {a : ℕ → ℤ} (ha : a 1 = 1) :
    ¬ (3 : ℤ) ∣ PowerSeries.coeff 1 (bridgeProduct a) := by
  rw [coeff_one_bridgeProduct, ha]
  intro h
  have h6 : (3 : ℤ) ∣ a 0 * (6 * EisensteinWeightOne.sigmaChi 1) :=
    Dvd.dvd.mul_left (Dvd.dvd.mul_right (by norm_num) _) _
  have h1 : (3 : ℤ) ∣ 1 := (dvd_add_right h6).mp (by simpa [add_comm] using h)
  omega

theorem latticeMk_realization_ne_zero {a : ℕ → ℤ} (ha : a 1 = 1) {f : Lat N}
    (hf : ∀ n, (3 : ℤ) ∣ PowerSeries.coeff n (intQExpansion f) - PowerSeries.coeff n (bridgeProduct a)) :
    latticeMk f ≠ 0 := by
  intro h0
  rw [latticeMk_eq_zero_iff] at h0
  have hF : (3 : ℤ) ∣ PowerSeries.coeff 1 (bridgeProduct a) := by
    have h1 := h0 1
    have h2 := hf 1
    have hsplit : PowerSeries.coeff 1 (bridgeProduct a)
        = PowerSeries.coeff 1 (intQExpansion f)
          - (PowerSeries.coeff 1 (intQExpansion f) - PowerSeries.coeff 1 (bridgeProduct a)) := by ring
    rw [hsplit]
    exact dvd_sub h1 h2
  exact not_three_dvd_coeff_one_bridgeProduct ha hF

theorem exists_lat_of_isLatticeRealized {a : ℕ → ℤ} (h : CuspForm.IsLatticeRealized N a) :
    ∃ f : Lat N, ∀ n, (3 : ℤ) ∣ PowerSeries.coeff n (intQExpansion f) - PowerSeries.coeff n (bridgeProduct a) := by
  obtain ⟨f, -, af, haf, hcong⟩ := h
  have hmem : f ∈ Lat N := (CuspForm.mem_intLattice_iff f).mpr fun n => ⟨af n, (haf n).symm⟩
  refine ⟨⟨f, hmem⟩, fun n => ?_⟩
  have hcast : ((PowerSeries.coeff n (intQExpansion ⟨f, hmem⟩) : ℤ) : ℂ) = (af n : ℂ) := by
    rw [intQExpansion_cast, haf n]
  rw [Int.cast_injective (α := ℂ) hcast]
  exact hcong n

section Clauses

variable [NeZero N]

theorem intQExpansion_latticeAction_T {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) (f : Lat N) :
    intQExpansion (latticeAction (CuspForm.heckeAlgebra.T hℓ hℓN hℓN) f)
      = PowerSeries.heckeT ℓ 2 (intQExpansion f) := by
  ext n
  have hcast : ((PowerSeries.coeff n (intQExpansion (latticeAction (CuspForm.heckeAlgebra.T hℓ hℓN hℓN) f)) : ℤ) : ℂ)
      = ((PowerSeries.coeff n (PowerSeries.heckeT ℓ 2 (intQExpansion f)) : ℤ) : ℂ) := by
    rw [intQExpansion_cast, latticeAction_apply_coe, CuspForm.heckeAlgebra.coe_T,
      CuspForm.coe_heckeTLin_apply, ModularFormClass.qCoeff_heckeT _ (hΓ N) hℓ.ne_zero,
      ModularForm.coeffHeckeT_apply, PowerSeries.coeff_heckeT]
    push_cast
    rw [intQExpansion_cast, mul_comm n ℓ]
    by_cases hdvd : ℓ ∣ n
    · rw [if_pos hdvd, if_pos hdvd, intQExpansion_cast]
      norm_num
    · rw [if_neg hdvd, if_neg hdvd]
      simp
  exact Int.cast_injective (α := ℂ) hcast

theorem heckeSMul_latticeReduction {a : ℕ → ℤ} {f : Lat N}
    (hf : ∀ n, (3 : ℤ) ∣ PowerSeries.coeff n (intQExpansion f) - PowerSeries.coeff n (bridgeProduct a))
    (m₀ : LatticeMod3 N) (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) :
    (CuspForm.heckeAlgebra.T hℓ hℓN hℓN - ((a ℓ : ℤ) : HA N)) • latticeReduction m₀ (bridgeProduct a)
      = latticeReduction m₀ (PowerSeries.heckeT ℓ 2 (bridgeProduct a) - a ℓ • bridgeProduct a) := by
  rw [latticeReduction_eq_mk m₀ hf, sub_smul, heckeSMul_mk, intCast_heckeSMul_mk, ← Submodule.Quotient.mk_sub]
  symm
  refine latticeReduction_eq_mk m₀ fun n => ?_
  rw [intQExpansion_sub, map_sub, intQExpansion_latticeAction_T, coeff_intQExpansion_zsmul, map_sub]
  have hsm : PowerSeries.coeff n (a ℓ • bridgeProduct a) = a ℓ * PowerSeries.coeff n (bridgeProduct a) := by
    rw [map_zsmul, zsmul_eq_mul, Int.cast_id]
  rw [hsm]

  have hH : (3 : ℤ) ∣ PowerSeries.coeff n (PowerSeries.heckeT ℓ 2 (intQExpansion f))
      - PowerSeries.coeff n (PowerSeries.heckeT ℓ 2 (bridgeProduct a)) := by
    rw [← map_sub, ← map_sub, PowerSeries.coeff_heckeT]
    refine dvd_add ?_ (Dvd.dvd.mul_left ?_ _)
    · simpa using hf (ℓ * n)
    · split_ifs
      · simpa using hf (n / ℓ)
      · simp
  have hS : (3 : ℤ) ∣ a ℓ * PowerSeries.coeff n (intQExpansion f) - a ℓ * PowerSeries.coeff n (bridgeProduct a) := by
    rw [← mul_sub]
    exact Dvd.dvd.mul_left (hf n) _
  have hsplit : PowerSeries.coeff n (PowerSeries.heckeT ℓ 2 (intQExpansion f))
        - a ℓ * PowerSeries.coeff n (intQExpansion f)
        - (PowerSeries.coeff n (PowerSeries.heckeT ℓ 2 (bridgeProduct a))
          - a ℓ * PowerSeries.coeff n (bridgeProduct a))
      = (PowerSeries.coeff n (PowerSeries.heckeT ℓ 2 (intQExpansion f))
          - PowerSeries.coeff n (PowerSeries.heckeT ℓ 2 (bridgeProduct a)))
        - (a ℓ * PowerSeries.coeff n (intQExpansion f) - a ℓ * PowerSeries.coeff n (bridgeProduct a)) := by
    ring
  rw [hsplit]
  exact dvd_sub hH hS

theorem three_heckeSMul_latticeReduction (m₀ : LatticeMod3 N) {a : ℕ → ℤ} {f : Lat N}
    (hf : ∀ n, (3 : ℤ) ∣ PowerSeries.coeff n (intQExpansion f) - PowerSeries.coeff n (bridgeProduct a)) :
    (3 : HA N) • latticeReduction m₀ (bridgeProduct a) = 0 := by
  rw [latticeReduction_eq_mk m₀ hf]
  have h3 : (3 : HA N) = ((3 : ℤ) : HA N) := by rw [Int.cast_ofNat]
  rw [h3, intCast_heckeSMul_mk, latticeMk_eq_zero_iff]
  intro n
  rw [coeff_intQExpansion_zsmul]
  exact dvd_mul_right 3 _

end Clauses

end CuspForm.S17C
p2m_reactivate "P2MW.S_CuspForm_exists_reductionModule_of_isLatticeRealized.CuspForm P2MW.S_CuspForm_exists_reductionModule_of_isLatticeRealized.CuspForm.S17C"
p2m_reactivate "P2MW.S_CuspForm_exists_reductionModule_of_isLatticeRealized.CuspForm"

end
p2m_reactivate "P2MW.S_CuspForm_exists_reductionModule_of_isLatticeRealized.CuspForm P2MW.S_CuspForm_exists_reductionModule_of_isLatticeRealized.CuspForm.S17C"

open CuspForm.S17C in
theorem solution {N : ℕ} [NeZero N] (hN : CuspForm.HasIntegralStructure N 2) {a : ℕ → ℤ} (h1 : a 1 = 1)
    (hreal : CuspForm.IsLatticeRealized N a) :
    ∃ (M : Type) (_ : AddCommGroup M) (_ : Module (CuspForm.heckeAlgebra N 2 {ℓ | ℓ ∣ N}) M)
      (red : PowerSeries ℤ → M),
      (∀ g, (∀ n, (3 : ℤ) ∣ PowerSeries.coeff n g) → red g = 0) ∧
      (∀ g, red g = 0 → (3 : ℤ) ∣ PowerSeries.coeff 1 g) ∧
      (3 : CuspForm.heckeAlgebra N 2 {ℓ | ℓ ∣ N}) • red (bridgeProduct a) = 0 ∧
      ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N),
        (CuspForm.heckeAlgebra.T hℓ hℓN hℓN - ((a ℓ : ℤ) : CuspForm.heckeAlgebra N 2 {ℓ | ℓ ∣ N}))
            • red (bridgeProduct a)
          = red (PowerSeries.heckeT ℓ 2 (bridgeProduct a) - a ℓ • bridgeProduct a) := by
  obtain ⟨fF, hfF⟩ := exists_lat_of_isLatticeRealized hreal
  exact ⟨LatticeMod3 N, inferInstance, inferInstance, latticeReduction (latticeMk fF),
    fun g hg => latticeReduction_eq_zero _ hg,
    fun g hg => latticeReduction_dvd_of_eq_zero (latticeMk_realization_ne_zero h1 hfF) g hg,
    three_heckeSMul_latticeReduction _ hfF,
    fun ℓ hℓ hℓN => heckeSMul_latticeReduction hfF _ ℓ hℓ hℓN⟩

end S_CuspForm_exists_reductionModule_of_isLatticeRealized
end P2MW
export P2MW.S_CuspForm_exists_reductionModule_of_isLatticeRealized (solution)
