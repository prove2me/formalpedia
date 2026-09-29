-- Prove2me | solution 1 for CuspForm.exists_isNormalizedEigenform_annihilator_le_of_isPrime
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/dcdd37aa-4a84-598e-acbc-5b252a585631

import Mathlib
import Definitions.Def_FLTPrelim_Modularity
import Definitions.Def_ModularForm_HeckeOperator
import Definitions.Def_ModularForm_HeckeOperatorForms
import Definitions.Def_CuspForm_HeckeAlgebra
import Theorems.Thm_CuspForm_finiteDimensional_Gamma0
import Theorems.Thm_CuspForm_heckeTLin_apply_eq_smul_iff
import Theorems.Thm_CuspForm_heckeULin_apply_eq_smul_iff
import Theorems.Thm_CuspForm_isNormalizedEigenform_iff_heckeTLin
import Theorems.Thm_ModularFormClass_eq_of_forall_qCoeff_eq
import Theorems.Thm_CuspForm_qCoeff_zero
import Theorems.Thm_CongruenceSubgroup_one_mem_strictPeriods_Gamma0
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CuspForm_exists_isNormalizedEigenform_annihilator_le_of_isPrime

set_option autoImplicit false
set_option maxHeartbeats 6400000

open Function

noncomputable section

namespace P2mWs11ER

section Socle

variable {K : Type*} [Field K] {A : Type*} [CommRing A] [Algebra K A] [Module.Finite K A]
variable {V : Type*} [AddCommGroup V] [Module K V]

include K in
theorem exists_pow_succ_eq (𝔪 : Ideal A) : ∃ n : ℕ, 0 < n ∧ 𝔪 ^ (n + 1) = 𝔪 ^ n := by
  haveI : IsArtinianRing A := IsArtinianRing.of_finite K A
  obtain ⟨n, hn⟩ := IsArtinian.monotone_stabilizes (R := A) (M := A)
    ⟨fun k => OrderDual.toDual (𝔪 ^ k), fun i j hij =>
      OrderDual.toDual_le_toDual.mpr (Ideal.pow_le_pow_right hij)⟩
  refine ⟨n + 1, Nat.succ_pos n, ?_⟩
  have h1 : 𝔪 ^ (n + 1) = 𝔪 ^ n := (OrderDual.toDual_inj.mp (hn (n + 1) (Nat.le_succ n))).symm
  have h2 : 𝔪 ^ (n + 2) = 𝔪 ^ n := (OrderDual.toDual_inj.mp (hn (n + 2) (by omega))).symm
  rw [h1, h2]

include K in
theorem exists_notMem_mul_eq_zero (𝔪 : Ideal A) (h𝔪 : 𝔪.IsMaximal) :
    ∃ (ε : A) (n : ℕ), 0 < n ∧ ε ∉ 𝔪 ∧ ∀ x ∈ 𝔪 ^ n, ε * x = 0 := by
  obtain ⟨n, hn0, hn⟩ := exists_pow_succ_eq (K := K) 𝔪
  haveI : IsNoetherian K A := IsNoetherian.iff_fg.mpr inferInstance
  haveI : IsNoetherianRing A := isNoetherian_of_tower K inferInstance
  obtain ⟨r, hr1, hr⟩ := Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul
    𝔪 (𝔪 ^ n) (IsNoetherian.noetherian _)
    (le_of_eq (by rw [Ideal.smul_eq_mul, ← pow_succ', hn]))
  refine ⟨r, n, hn0, fun hr𝔪 => h𝔪.ne_top ?_, fun x hx => by simpa using hr x hx⟩
  exact (Ideal.eq_top_iff_one 𝔪).mpr (by simpa using 𝔪.sub_mem hr𝔪 hr1)

variable (ρ : A →ₐ[K] Module.End K V)

omit [Module.Finite K A] in
theorem exists_forall_mem_apply_eq_zero_of_pow (𝔪 : Ideal A) :
    ∀ (j : ℕ) (w : V), w ≠ 0 → (∀ T ∈ 𝔪 ^ j, ρ T w = 0) →
      ∃ u : V, u ≠ 0 ∧ ∀ S ∈ 𝔪, ρ S u = 0 := by
  intro j
  induction j with
  | zero =>
    intro w hw hjw
    refine absurd ?_ hw
    simpa using hjw 1 (by simp)
  | succ j ih =>
    intro w hw hjw
    by_cases hsoc : ∀ S ∈ 𝔪, ρ S w = 0
    · exact ⟨w, hw, hsoc⟩
    · obtain ⟨S, hS⟩ := not_forall.mp hsoc
      obtain ⟨hS𝔪, hSw⟩ := _root_.not_imp.mp hS
      refine ih (ρ S w) hSw fun T hT => ?_
      have hTS : T * S ∈ 𝔪 ^ (j + 1) := by
        rw [pow_succ]
        exact Ideal.mul_mem_mul hT hS𝔪
      have hcomp : ρ T (ρ S w) = ρ (T * S) w := by rw [map_mul]; rfl
      rw [hcomp]
      exact hjw _ hTS

theorem exists_forall_mem_apply_eq_zero (hρ : Function.Injective ρ)
    (𝔪 : Ideal A) (h𝔪 : 𝔪.IsMaximal) :
    ∃ v : V, v ≠ 0 ∧ ∀ T ∈ 𝔪, ρ T v = 0 := by
  obtain ⟨ε, n, _, hε𝔪, hε⟩ := exists_notMem_mul_eq_zero (K := K) 𝔪 h𝔪
  have hε0 : ε ≠ 0 := fun h => hε𝔪 (h ▸ 𝔪.zero_mem)
  have hρε : ρ ε ≠ 0 := fun h => hε0 (hρ (by rw [h, map_zero]))
  obtain ⟨v, hv⟩ : ∃ v : V, ρ ε v ≠ 0 := by
    by_contra h
    exact hρε (LinearMap.ext fun v => not_not.mp fun hv => h ⟨v, hv⟩)
  refine exists_forall_mem_apply_eq_zero_of_pow ρ 𝔪 n (ρ ε v) hv fun T hT => ?_
  have hcomp : ρ T (ρ ε v) = ρ (T * ε) v := by rw [map_mul]; rfl
  rw [hcomp, mul_comm, hε T hT, map_zero]
  rfl

end Socle

open CuspForm ModularForm ModularFormClass

section Hecke

variable (N : ℕ) [NeZero N]

abbrev S2 : Type := CuspForm (CongruenceSubgroup.Gamma0 N) 2

def fullC : Subalgebra ℂ (Module.End ℂ (S2 N)) :=
  Algebra.adjoin ℂ (CuspForm.heckeGenerators N 2 (∅ : Set ℕ))

scoped instance fullC.instIsMulCommutative : IsMulCommutative (fullC N) :=
  Algebra.isMulCommutative_adjoin ℂ fun _ hT _ hT' => CuspForm.commute_of_mem_heckeGenerators hT hT'

p2m_reactivate "P2MW.S_CuspForm_exists_isNormalizedEigenform_annihilator_le_of_isPrime.P2mWs11ER.fullC"
open scoped IsMulCommutative in
scoped instance fullC.instCommRing : CommRing (fullC N) := inferInstance

p2m_reactivate "P2MW.S_CuspForm_exists_isNormalizedEigenform_annihilator_le_of_isPrime.P2mWs11ER.fullC"
scoped instance fullC.instModuleFinite : Module.Finite ℂ (fullC N) := by
  haveI : FiniteDimensional ℂ (S2 N) := CuspForm.finiteDimensional_Gamma0 N 2
  exact Module.Finite.iff_fg.mpr (IsNoetherian.noetherian (Subalgebra.toSubmodule (fullC N)))

p2m_reactivate "P2MW.S_CuspForm_exists_isNormalizedEigenform_annihilator_le_of_isPrime.P2mWs11ER.fullC"
variable {N}

set_option synthInstance.maxHeartbeats 1600000 in

theorem exists_sub_algebraMap_mem (𝔪 : Ideal (fullC N)) (h𝔪 : 𝔪.IsMaximal) (T : fullC N) :
    ∃ c : ℂ, T - algebraMap ℂ (fullC N) c ∈ 𝔪 := by
  haveI := h𝔪
  letI : Field (fullC N ⧸ 𝔪) := Ideal.Quotient.field 𝔪
  haveI : Module.Finite ℂ (fullC N ⧸ 𝔪) :=
    Module.Finite.of_surjective (Ideal.Quotient.mkₐ ℂ 𝔪).toLinearMap Ideal.Quotient.mk_surjective
  haveI : Algebra.IsIntegral ℂ (fullC N ⧸ 𝔪) := Algebra.IsIntegral.of_finite ℂ _
  obtain ⟨c, hc⟩ := (IsAlgClosed.algebraMap_bijective_of_isIntegral
    (k := ℂ) (K := fullC N ⧸ 𝔪)).2 (Ideal.Quotient.mk 𝔪 T)
  refine ⟨c, ?_⟩
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, sub_eq_zero, ← hc, ← Ideal.Quotient.algebraMap_eq,
    ← IsScalarTower.algebraMap_apply ℂ (fullC N) (fullC N ⧸ 𝔪)]

variable {g : S2 N}

theorem qCoeff_eq_zero_of_qCoeff_one_eq_zero
    (hT : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N), ∃ c : ℂ, CuspForm.heckeTLin 2 hℓ hℓN g = c • g)
    (hU : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ℓ ∣ N), ∃ c : ℂ, CuspForm.heckeULin 2 hℓN g = c • g)
    (h1 : qCoeff g 1 = 0) : ∀ n : ℕ, qCoeff g n = 0 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n, ih with
    | 0, _ => exact CuspForm.qCoeff_zero g
    | 1, _ => exact h1
    | (m + 2), ih =>
      obtain ⟨ℓ, hℓ, hℓdvd⟩ := Nat.exists_prime_and_dvd (n := m + 2) (by omega)
      obtain ⟨d, hd⟩ := hℓdvd
      have hℓ2 : 2 ≤ ℓ := hℓ.two_le
      have hd0 : d ≠ 0 := by rintro rfl; omega
      have hdlt : d < m + 2 := by
        rcases Nat.lt_or_ge d (m + 2) with h | h
        · exact h
        · exfalso; nlinarith
      by_cases hℓN : ℓ ∣ N
      · obtain ⟨c, hc⟩ := hU ℓ hℓ hℓN
        have key := (CuspForm.heckeULin_apply_eq_smul_iff 2 hℓN g c).mp hc d
        rw [ModularForm.coeffHeckeU_apply, ih d hdlt, mul_zero] at key
        rw [hd, mul_comm, key]
      · obtain ⟨c, hc⟩ := hT ℓ hℓ hℓN
        have key := (CuspForm.heckeTLin_apply_eq_smul_iff 2 hℓ hℓN g c).mp hc d
        rw [ModularForm.coeffHeckeT_apply, ih d hdlt, mul_zero] at key
        have htail : (if ℓ ∣ d then (ℓ : ℂ) ^ ((2 : ℤ) - 1) * qCoeff g (d / ℓ) else 0) = 0 := by
          split_ifs with hdvd
          · rw [ih (d / ℓ) (lt_of_le_of_lt (Nat.div_le_self d ℓ) hdlt), mul_zero]
          · rfl
        rw [htail, add_zero] at key
        rw [hd, mul_comm, key]

theorem qCoeff_one_ne_zero_of_ne_zero
    (hT : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N), ∃ c : ℂ, CuspForm.heckeTLin 2 hℓ hℓN g = c • g)
    (hU : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ℓ ∣ N), ∃ c : ℂ, CuspForm.heckeULin 2 hℓN g = c • g)
    (hg : g ≠ 0) : qCoeff g 1 ≠ 0 := by
  intro h1
  refine hg (ModularFormClass.eq_of_forall_qCoeff_eq
    (CongruenceSubgroup.one_mem_strictPeriods_Gamma0 N) fun n => ?_)
  rw [qCoeff_eq_zero_of_qCoeff_one_eq_zero hT hU h1 n]
  show (0 : ℂ) = qCoeff (⇑(0 : S2 N)) n
  rw [CuspForm.coe_zero]
  simp [ModularFormClass.qCoeff, UpperHalfPlane.qExpansion_zero]

theorem smul_eigen_T {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) {c : ℂ} (a : ℂ)
    (h : CuspForm.heckeTLin 2 hℓ hℓN g = c • g) :
    CuspForm.heckeTLin 2 hℓ hℓN (a • g) = c • (a • g) := by
  rw [map_smul, h, smul_comm]

theorem smul_eigen_U {ℓ : ℕ} (hℓN : ℓ ∣ N) {c : ℂ} (a : ℂ)
    (h : CuspForm.heckeULin 2 hℓN g = c • g) :
    CuspForm.heckeULin 2 hℓN (a • g) = c • (a • g) := by
  rw [map_smul, h, smul_comm]

theorem exists_isNormalizedEigenform_smul_eq
    (hT : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N), ∃ c : ℂ, CuspForm.heckeTLin 2 hℓ hℓN g = c • g)
    (hU : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ℓ ∣ N), ∃ c : ℂ, CuspForm.heckeULin 2 hℓN g = c • g)
    (hg : g ≠ 0) :
    ∃ f : S2 N, f.IsNormalizedEigenform ∧ ∃ a : ℂ, a ≠ 0 ∧ f = a • g := by
  have ha := qCoeff_one_ne_zero_of_ne_zero hT hU hg
  set a : ℂ := (qCoeff g 1)⁻¹ with ha_def
  have ha0 : a ≠ 0 := inv_ne_zero ha

  have hTf : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N),
      ∃ c : ℂ, CuspForm.heckeTLin 2 hℓ hℓN (a • g) = c • (a • g) :=
    fun ℓ hℓ hℓN => by obtain ⟨c, hc⟩ := hT ℓ hℓ hℓN; exact ⟨c, smul_eigen_T hℓ hℓN a hc⟩
  have hUf : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ℓ ∣ N),
      ∃ c : ℂ, CuspForm.heckeULin 2 hℓN (a • g) = c • (a • g) :=
    fun ℓ hℓ hℓN => by obtain ⟨c, hc⟩ := hU ℓ hℓ hℓN; exact ⟨c, smul_eigen_U hℓN a hc⟩

  have hsmul : ∀ n : ℕ, qCoeff (⇑(a • g)) n = a * qCoeff g n := by
    intro n
    have han : AnalyticAt ℂ (UpperHalfPlane.cuspFunction 1 ⇑g) 0 :=
      ModularFormClass.analyticAt_cuspFunction_zero g one_pos
        (CongruenceSubgroup.one_mem_strictPeriods_Gamma0 N)
    show (UpperHalfPlane.qExpansion 1 ⇑(a • g)).coeff n = a * (UpperHalfPlane.qExpansion 1 ⇑g).coeff n
    rw [show (⇑(a • g) : UpperHalfPlane → ℂ) = a • ⇑g from rfl, UpperHalfPlane.qExpansion_smul han]
    simp
  have hf1 : qCoeff (⇑(a • g)) 1 = 1 := by rw [hsmul, ha_def, inv_mul_cancel₀ ha]
  refine ⟨a • g, ?_, a, ha0, rfl⟩
  rw [CuspForm.isNormalizedEigenform_iff_heckeTLin]
  refine ⟨hf1, fun p hp => ⟨fun hpN => ?_, fun hpN => ?_⟩⟩
  · obtain ⟨c, hc⟩ := hTf p hp hpN
    have hc1 := (CuspForm.heckeTLin_apply_eq_smul_iff 2 hp hpN (a • g) c).mp hc 1
    rw [ModularForm.coeffHeckeT_apply, one_mul, if_neg (fun h => hp.ne_one (Nat.dvd_one.mp h)),
      add_zero, hf1, mul_one] at hc1
    rw [hc, ← hc1]
  · obtain ⟨c, hc⟩ := hUf p hp hpN
    have hc1 := (CuspForm.heckeULin_apply_eq_smul_iff 2 hpN (a • g) c).mp hc 1
    rw [ModularForm.coeffHeckeU_apply, one_mul, hf1, mul_one] at hc1
    rw [hc, ← hc1]

theorem exists_isNormalizedEigenform_of_isMaximal (𝔪 : Ideal (fullC N)) (h𝔪 : 𝔪.IsMaximal) :
    ∃ f : S2 N, f.IsNormalizedEigenform ∧ ∀ T ∈ 𝔪, ((fullC N).val T) f = 0 := by
  obtain ⟨g, hg0, hg⟩ := exists_forall_mem_apply_eq_zero (K := ℂ) (fullC N).val Subtype.val_injective 𝔪 h𝔪
  have heigen : ∀ T : fullC N, ∃ c : ℂ, ((fullC N).val T) g = c • g := by
    intro T
    obtain ⟨c, hc⟩ := exists_sub_algebraMap_mem 𝔪 h𝔪 T
    refine ⟨c, ?_⟩
    have h0 : ((fullC N).val (T - algebraMap ℂ (fullC N) c)) g = 0 := hg _ hc
    rw [map_sub, AlgHom.commutes, LinearMap.sub_apply, sub_eq_zero, Module.algebraMap_end_apply] at h0
    exact h0
  have hTgen : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N), ∃ c : ℂ, CuspForm.heckeTLin 2 hℓ hℓN g = c • g := by
    intro ℓ hℓ hℓN
    exact heigen ⟨CuspForm.heckeTLin 2 hℓ hℓN, Algebra.subset_adjoin
      (CuspForm.heckeTLin_mem_heckeGenerators hℓ hℓN (by simp))⟩
  have hUgen : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ℓ ∣ N), ∃ c : ℂ, CuspForm.heckeULin 2 hℓN g = c • g := by
    intro ℓ hℓ hℓN
    exact heigen ⟨CuspForm.heckeULin 2 hℓN, Algebra.subset_adjoin
      (CuspForm.heckeULin_mem_heckeGenerators hℓ hℓN (by simp))⟩
  obtain ⟨f, hf, a, ha0, hfa⟩ := exists_isNormalizedEigenform_smul_eq hTgen hUgen hg0
  refine ⟨f, hf, fun T hT => ?_⟩
  rw [hfa, map_smul, hg T hT, smul_zero]

theorem coe_mem_fullC (S : Set ℕ) (t : CuspForm.heckeAlgebra N 2 S) :
    (t : Module.End ℂ (S2 N)) ∈ fullC N := by
  have hle : CuspForm.heckeAlgebra N 2 S ≤ (fullC N).restrictScalars ℤ := by
    refine Algebra.adjoin_le ?_
    intro T hT
    exact Algebra.subset_adjoin (CuspForm.heckeGenerators_mono (Set.empty_subset S) hT)
  exact hle t.2

theorem isNilpotent_of_forall_apply_eq_zero
    (F : ∀ 𝔪 : Ideal (fullC N), 𝔪.IsMaximal → S2 N)
    (hF0 : ∀ 𝔪 h𝔪, F 𝔪 h𝔪 ≠ 0)
    (hF : ∀ 𝔪 h𝔪, ∀ T ∈ 𝔪, ((fullC N).val T) (F 𝔪 h𝔪) = 0)
    (x : fullC N) (hx : ∀ 𝔪 h𝔪, ((fullC N).val x) (F 𝔪 h𝔪) = 0) :
    IsNilpotent x := by
  haveI : IsArtinianRing (fullC N) := IsArtinianRing.of_finite ℂ _
  rw [← mem_nilradical, nilradical_eq_sInf]
  refine Submodule.mem_sInf.mpr fun 𝔮 h𝔮 => ?_
  haveI : Ideal.IsPrime 𝔮 := h𝔮
  have h𝔮max : Ideal.IsMaximal 𝔮 := IsArtinianRing.isMaximal_of_isPrime 𝔮
  by_contra hx𝔮
  obtain ⟨z, m, hm, hzm⟩ := h𝔮max.exists_inv hx𝔮
  have happ : ((fullC N).val (z * x + m)) (F 𝔮 h𝔮max) = F 𝔮 h𝔮max := by
    rw [hzm]
    rfl
  rw [map_add, map_mul, LinearMap.add_apply, Module.End.mul_apply, hx 𝔮 h𝔮max, map_zero,
    zero_add, hF 𝔮 h𝔮max m hm] at happ
  exact hF0 𝔮 h𝔮max happ.symm

end Hecke
p2m_reactivate "P2MW.S_CuspForm_exists_isNormalizedEigenform_annihilator_le_of_isPrime.P2mWs11ER.fullC"

end P2mWs11ER
p2m_reactivate "P2MW.S_CuspForm_exists_isNormalizedEigenform_annihilator_le_of_isPrime.P2mWs11ER.fullC P2MW.S_CuspForm_exists_isNormalizedEigenform_annihilator_le_of_isPrime.P2mWs11ER"

open P2mWs11ER in
theorem solution {N : ℕ} [NeZero N]
    (S : Set ℕ) (𝔭 : Ideal (CuspForm.heckeAlgebra N 2 S)) (h𝔭 : 𝔭.IsPrime) :
    ∃ f : CuspForm (CongruenceSubgroup.Gamma0 N) 2, f.IsNormalizedEigenform ∧
      ∀ t : CuspForm.heckeAlgebra N 2 S,
        (t : Module.End ℂ (CuspForm (CongruenceSubgroup.Gamma0 N) 2)) f = 0 → t ∈ 𝔭 := by
  classical
  haveI := h𝔭

  have hchoice : ∀ 𝔪 : {I : Ideal (fullC N) // I.IsMaximal},
      ∃ f : S2 N, f.IsNormalizedEigenform ∧ ∀ T ∈ 𝔪.1, ((fullC N).val T) f = 0 :=
    fun 𝔪 => exists_isNormalizedEigenform_of_isMaximal 𝔪.1 𝔪.2
  choose F hF1 hF2 using hchoice
  haveI : IsArtinianRing (fullC N) := IsArtinianRing.of_finite ℂ _
  haveI : Finite {I : Ideal (fullC N) // I.IsMaximal} :=
    (IsArtinianRing.setOf_isMaximal_finite (fullC N)).to_subtype
  haveI : Fintype {I : Ideal (fullC N) // I.IsMaximal} := Fintype.ofFinite _
  have hF0 : ∀ 𝔪 : {I : Ideal (fullC N) // I.IsMaximal}, F 𝔪 ≠ 0 := by
    intro 𝔪 h0
    have h1 := (hF1 𝔪).qCoeff_one
    rw [h0, CuspForm.coe_zero] at h1
    simp [ModularFormClass.qCoeff, UpperHalfPlane.qExpansion_zero] at h1
  by_contra hcon

  have hwit : ∀ 𝔪 : {I : Ideal (fullC N) // I.IsMaximal},
      ∃ y : CuspForm.heckeAlgebra N 2 S, (y : Module.End ℂ (S2 N)) (F 𝔪) = 0 ∧ y ∉ 𝔭 := by
    intro 𝔪
    by_contra hy
    exact hcon ⟨F 𝔪, hF1 𝔪, fun t ht => not_not.mp fun hnt => hy ⟨t, ht, hnt⟩⟩
  choose y hy1 hy2 using hwit
  set x : CuspForm.heckeAlgebra N 2 S := ∏ 𝔪, y 𝔪 with hx_def
  have hx𝔭 : x ∉ 𝔭 := by
    intro hx
    obtain ⟨𝔪, _, h𝔪⟩ := Ideal.IsPrime.prod_mem_iff.mp hx
    exact hy2 𝔪 h𝔪
  have hxkill : ∀ 𝔪 : {I : Ideal (fullC N) // I.IsMaximal}, (x : Module.End ℂ (S2 N)) (F 𝔪) = 0 := by
    intro 𝔪
    have hperm : x = (∏ 𝔪' ∈ Finset.univ.erase 𝔪, y 𝔪') * y 𝔪 := by
      rw [hx_def, Finset.prod_erase_mul _ _ (Finset.mem_univ 𝔪)]
    rw [hperm, Subalgebra.coe_mul, Module.End.mul_apply, hy1 𝔪, map_zero]

  let x' : fullC N := ⟨(x : Module.End ℂ (S2 N)), coe_mem_fullC S x⟩
  have hnil : IsNilpotent x' :=
    isNilpotent_of_forall_apply_eq_zero (fun 𝔪 h𝔪 => F ⟨𝔪, h𝔪⟩) (fun 𝔪 h𝔪 => hF0 ⟨𝔪, h𝔪⟩)
      (fun 𝔪 h𝔪 => hF2 ⟨𝔪, h𝔪⟩) x' (fun 𝔪 h𝔪 => hxkill ⟨𝔪, h𝔪⟩)
  obtain ⟨k, hk⟩ := hnil
  have hxk : x ^ k = 0 := by
    apply Subtype.ext
    have := congrArg Subtype.val hk
    simpa [x'] using this
  exact hx𝔭 (h𝔭.mem_of_pow_mem k (by rw [hxk]; exact 𝔭.zero_mem))

end
end S_CuspForm_exists_isNormalizedEigenform_annihilator_le_of_isPrime
end P2MW
export P2MW.S_CuspForm_exists_isNormalizedEigenform_annihilator_le_of_isPrime (solution)
