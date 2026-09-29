-- Prove2me | solution 1 for CuspForm.IsPrimitiveForm.level_eq_and_qCoeff_eq_of_forall_prime_notMem_qCoeff_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/20694d01-d928-5e94-a1f0-26faec3a8cac

import Mathlib
import Definitions.Def_FLTPrelim_Modularity
import Definitions.Def_CuspForm_PrimitiveFormGamma1
import Theorems.Thm_CuspForm_eq_smul_of_isPrimitiveForm_of_qCoeff_hecke_eigen
import Theorems.Thm_CuspForm_exists_qCoeff_eq_sum_isPrimitiveForm_of_hasNebentypus
import Theorems.Thm_CuspForm_exists_hasNebentypus_qCoeff_eq_sum_primeFactors_of_forall_coprime_qCoeff_eq_zero
import Theorems.Thm_CuspForm_exists_degeneracy_gamma1_hasNebentypus
import Theorems.Thm_CuspForm_qCoeff_sq_eq_mul_zpow_or_exists_hasNebentypus_qCoeff_hecke_eigen_of_dvd_of_not_sq_dvd
import Theorems.Thm_CuspForm_norm_sq_lt_of_hasNebentypus_qCoeff_hecke_eigen
import Theorems.Thm_CuspForm_IsPrimitiveForm_pow_dvd_of_pow_dvd_of_sq_dvd_of_factorsThrough_of_forall_coprime_qCoeff_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CuspForm_IsPrimitiveForm_level_eq_and_qCoeff_eq_of_forall_prime_notMem_qCoeff_eq
p2m_attr_erase "instance" "FLT.HyperbolicMeasure.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatIntUpperHalfPlaneVolume_definitions FLT.HyperbolicMeasure.instIsOpenPosMeasureUpperHalfPlaneVolume_definitions FLT.Gamma0FundamentalSet.instContinuousConstSMulSpecialLinearGroupFinOfNatNatIntUpperHalfPlane_definitions FLT.L2ProductionInstance.isFiniteMeasure_gamma0 FLT.L2ProductionInstance.countable_SL2Z FLT.L2ProductionInstance.countable_quotient FLT.L2ProductionInstance.nontrivial_gamma0L2 Ihara.instGroupIharaAmalgam"
p2m_attr_erase "simp" "FLT.TruncatedDomainPartition.unipotentDiagonalSum_zero Ihara.wConj_coe Ihara.wConj_symm_coe Ihara.coe_iota1 Ihara.coe_iota1SL Ihara.iota1Mat_apply_one_zero Ihara.iota1Mat_apply_zero_zero Ihara.iota1Mat_apply_zero_one Ihara.iota1Mat_apply_one_one Ihara.coe_iota0 Ihara.iharaEdge_one Ihara.pairFamily_zero Ihara.iharaEdge_zero Ihara.pairFamily_one Ihara.coe_amalgamToGamma0Away Ihara.coe_vertexZero Ihara.coe_slToAway FreyPackage.ModMCarrier.coe_rescaleLin_apply ModularForm.AtkinLehnerDatum.mk.injEq ModularForm.AtkinLehnerDatum.alGL_coe ModularForm.AtkinLehnerDatum.mk.sizeOf_spec ModularForm.AtkinLehnerDatum.sqUnitSL_coe ModularForm.AtkinLehnerDatum.det_sqUnit ModularForm.AtkinLehnerDatum.det_mat CuspForm.PeterssonCoset.mapGL_apply"

set_option autoImplicit false
set_option maxHeartbeats 3200000

open CongruenceSubgroup ModularFormClass UpperHalfPlane Function
open scoped MatrixGroups

noncomputable section

namespace SMOGamma1

local notation "Γ₁ℝ" M => ((Gamma1 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))

theorem exists_coeff_restrict {K V P ι : Type*} [Field K] [AddCommGroup V] [Module K V]
    (T : P → V →ₗ[K] V) (v : ι → V) (β : ι → P → K) (α : P → K) (s : Finset ι) :
    ∀ c : ι → K,
      (∀ i ∈ s, ∀ p, T p (v i) = β i p • v i) →
      (∀ p, T p (∑ i ∈ s, c i • v i) = α p • ∑ i ∈ s, c i • v i) →
      ∃ c' : ι → K, (∀ i ∈ s, c' i ≠ 0 → β i = α) ∧
        ∑ i ∈ s, c i • v i = ∑ i ∈ s, c' i • v i := by
  classical
  induction s using Finset.strongInduction with
  | H s ih =>
    intro c hv hw
    by_cases hall : ∀ i ∈ s, c i ≠ 0 → β i = α
    · exact ⟨c, hall, rfl⟩
    push Not at hall
    obtain ⟨j, hj, -, hβj⟩ := hall
    obtain ⟨p₀, hp₀⟩ : ∃ p₀, β j p₀ ≠ α p₀ := by
      by_contra hcon
      push Not at hcon
      exact hβj (funext hcon)
    set w : V := ∑ i ∈ s, c i • v i with hwdef
    have hne : α p₀ - β j p₀ ≠ 0 := sub_ne_zero.2 (Ne.symm hp₀)
    set c₁ : ι → K := fun i => (α p₀ - β j p₀)⁻¹ * (c i * (β i p₀ - β j p₀)) with hc₁
    have h2 : ∑ i ∈ s, (c i * (β i p₀ - β j p₀)) • v i = T p₀ w - β j p₀ • w := by
      rw [hwdef, map_sum, Finset.smul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i hi => ?_
      rw [map_smul, hv i hi p₀, smul_smul, smul_smul, ← sub_smul]
      congr 1
      ring
    have hsum : ∑ i ∈ s, c₁ i • v i = w := by
      have h3 : ∑ i ∈ s, c₁ i • v i =
          (α p₀ - β j p₀)⁻¹ • ∑ i ∈ s, (c i * (β i p₀ - β j p₀)) • v i := by
        rw [Finset.smul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [smul_smul]
      rw [h3, h2, hw p₀, ← sub_smul, smul_smul, inv_mul_cancel₀ hne, one_smul]
    have hc₁j : c₁ j = 0 := by simp [hc₁]
    have herase : ∑ i ∈ s.erase j, c₁ i • v i = ∑ i ∈ s, c₁ i • v i :=
      Finset.sum_erase _ (by rw [hc₁j, zero_smul])
    have hv' : ∀ i ∈ s.erase j, ∀ p, T p (v i) = β i p • v i :=
      fun i hi p => hv i (Finset.mem_of_mem_erase hi) p
    have hw' : ∀ p, T p (∑ i ∈ s.erase j, c₁ i • v i) = α p • ∑ i ∈ s.erase j, c₁ i • v i := by
      intro p
      rw [herase, hsum]
      exact hw p
    obtain ⟨c', h2', h3⟩ := ih (s.erase j) (Finset.erase_ssubset hj) c₁ hv' hw'
    refine ⟨fun i => if i = j then 0 else c' i, ?_, ?_⟩
    · intro i hi hne'
      change (if i = j then 0 else c' i) ≠ 0 at hne'
      by_cases hij : i = j
      · rw [if_pos hij] at hne'
        exact absurd rfl hne'
      · rw [if_neg hij] at hne'
        exact h2' i (Finset.mem_erase.2 ⟨hij, hi⟩) hne'
    · have hjz : (fun i => (if i = j then 0 else c' i) • v i) j = 0 := by
        show (if j = j then 0 else c' j) • v j = 0
        rw [if_pos rfl, zero_smul]
      rw [← hsum, ← herase, h3, ← Finset.sum_erase s hjz]
      refine Finset.sum_congr rfl fun i hi => ?_
      show c' i • v i = (if i = j then 0 else c' i) • v i
      rw [if_neg (Finset.ne_of_mem_erase hi)]

def heckeSeq (k : ℤ) (e : ℕ → ℂ) (p : ℕ) : (ℕ → ℂ) →ₗ[ℂ] (ℕ → ℂ) where
  toFun s := fun n => s (p * n) + e p * (p : ℂ) ^ (k - 1) * (if p ∣ n then s (n / p) else 0)
  map_add' s t := by
    funext n
    simp only [Pi.add_apply]
    split_ifs <;> ring
  map_smul' c s := by
    funext n
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    split_ifs <;> ring

theorem heckeSeq_apply (k : ℤ) (e : ℕ → ℂ) (p : ℕ) (s : ℕ → ℂ) (n : ℕ) :
    heckeSeq k e p s n = s (p * n) + e p * (p : ℂ) ^ (k - 1) * (if p ∣ n then s (n / p) else 0) :=
  rfl

def stretchSeq (d : ℕ) (b : ℕ → ℂ) : ℕ → ℂ := fun n => if d ∣ n then b (n / d) else 0

theorem stretchSeq_apply (d : ℕ) (b : ℕ → ℂ) (n : ℕ) :
    stretchSeq d b n = if d ∣ n then b (n / d) else 0 := rfl

theorem heckeSeq_stretchSeq {k : ℤ} {e : ℕ → ℂ} {p d : ℕ} (hp0 : p ≠ 0) (hd : d ≠ 0)
    (hpd : Nat.Coprime p d)
    {b : ℕ → ℂ} {lam : ℂ}
    (hb : ∀ m : ℕ, b (p * m) + e p * (p : ℂ) ^ (k - 1) * (if p ∣ m then b (m / p) else 0) = lam * b m) :
    heckeSeq k e p (stretchSeq d b) = lam • stretchSeq d b := by
  have hdpos : 0 < d := Nat.pos_of_ne_zero hd
  have hppos : 0 < p := Nat.pos_of_ne_zero hp0
  funext n
  simp only [heckeSeq_apply, Pi.smul_apply, smul_eq_mul, stretchSeq_apply]
  by_cases hdn : d ∣ n
  · obtain ⟨m, rfl⟩ := hdn
    have h1 : d ∣ p * (d * m) := ⟨p * m, by ring⟩
    have h2 : p * (d * m) / d = p * m := by
      rw [show p * (d * m) = d * (p * m) by ring, Nat.mul_div_cancel_left _ hdpos]
    have h3 : d * m / d = m := Nat.mul_div_cancel_left _ hdpos
    rw [if_pos h1, h2, if_pos (dvd_mul_right d m), h3]
    by_cases hpm : p ∣ m
    · obtain ⟨r, rfl⟩ := hpm
      have h4 : p ∣ d * (p * r) := ⟨d * r, by ring⟩
      have h5 : d * (p * r) / p = d * r := by
        rw [show d * (p * r) = p * (d * r) by ring, Nat.mul_div_cancel_left _ hppos]
      rw [if_pos h4, h5, if_pos (dvd_mul_right d r), Nat.mul_div_cancel_left _ hdpos]
      have := hb (p * r)
      rw [if_pos (dvd_mul_right p r), Nat.mul_div_cancel_left _ hppos] at this
      exact this
    · have h4 : ¬ p ∣ d * m := fun h => hpm (hpd.dvd_of_dvd_mul_left h)
      rw [if_neg h4]
      have := hb m
      rw [if_neg hpm] at this
      exact this
  · have h1 : ¬ d ∣ p * n := fun h => hdn ((Nat.Coprime.symm hpd).dvd_of_dvd_mul_left h)
    rw [if_neg h1, if_neg hdn, mul_zero]
    have hmid : (if p ∣ n then (if d ∣ n / p then b (n / p / d) else 0) else 0) = 0 := by
      split_ifs with hpn hdnp
      · exact absurd (dvd_trans hdnp (Nat.div_dvd_of_dvd hpn)) hdn
      · rfl
      · rfl
    rw [hmid, mul_zero, add_zero]

def copSeq (L' : ℕ) (s : ℕ → ℂ) : ℕ → ℂ := fun n => if Nat.Coprime n L' then s n else 0

theorem copSeq_apply (L' : ℕ) (s : ℕ → ℂ) (n : ℕ) :
    copSeq L' s n = if Nat.Coprime n L' then s n else 0 := rfl

theorem copSeq_smul (L' : ℕ) (c : ℂ) (s : ℕ → ℂ) : copSeq L' (c • s) = c • copSeq L' s := by
  funext n
  simp only [copSeq_apply, Pi.smul_apply, smul_eq_mul]
  split_ifs <;> ring

theorem heckeSeq_copSeq {k : ℤ} {e : ℕ → ℂ} {p L' : ℕ} (hp0 : p ≠ 0) (hp : Nat.Coprime p L')
    (s : ℕ → ℂ) : heckeSeq k e p (copSeq L' s) = copSeq L' (heckeSeq k e p s) := by
  have hppos : 0 < p := Nat.pos_of_ne_zero hp0
  funext n
  simp only [heckeSeq_apply, copSeq_apply]
  by_cases hn : Nat.Coprime n L'
  · rw [if_pos hn, if_pos (Nat.Coprime.mul_left hp hn)]
    by_cases hpn : p ∣ n
    · obtain ⟨r, rfl⟩ := hpn
      have hr : Nat.Coprime r L' := Nat.Coprime.coprime_dvd_left (Dvd.intro_left p rfl) hn
      rw [if_pos (dvd_mul_right p r), if_pos (dvd_mul_right p r), Nat.mul_div_cancel_left _ hppos,
        if_pos hr]
    · rw [if_neg hpn, if_neg hpn]
  · rw [if_neg hn]
    have h1 : ¬ Nat.Coprime (p * n) L' := fun h =>
      hn (Nat.Coprime.coprime_dvd_left (Dvd.intro_left p rfl) h)
    rw [if_neg h1]
    have hmid : (if p ∣ n then (if Nat.Coprime (n / p) L' then s (n / p) else 0) else 0) = 0 := by
      split_ifs with hpn hcop
      · exfalso
        obtain ⟨r, rfl⟩ := hpn
        rw [Nat.mul_div_cancel_left _ hppos] at hcop
        exact hn (Nat.Coprime.mul_left hp hcop)
      · rfl
      · rfl
    rw [hmid, mul_zero, add_zero]

theorem changeLevel_apply_natCast {M N : ℕ} [NeZero N] (hMN : M ∣ N) (εM : DirichletCharacter ℂ M)
    (ε : DirichletCharacter ℂ N) (h : DirichletCharacter.changeLevel hMN εM = ε)
    (p : ℕ) (hp : Nat.Coprime p N) :
    εM (p : ZMod M) = ε (p : ZMod N) := by
  haveI : NeZero M := ⟨fun h0 => by
    subst h0
    exact (NeZero.ne N) (Nat.eq_zero_of_zero_dvd hMN)⟩
  set u : (ZMod N)ˣ := ZMod.unitOfCoprime p hp with hu
  have hu' : (u : ZMod N) = (p : ZMod N) := ZMod.coe_unitOfCoprime p hp
  rw [← h, ← hu', DirichletCharacter.changeLevel_eq_cast_of_dvd εM hMN u, hu', ZMod.cast_natCast hMN]

section QCoeff

variable {L : ℕ} {k : ℤ}

theorem one_mem_strictPeriods (L : ℕ) : (1 : ℝ) ∈ (Γ₁ℝ L).strictPeriods := by
  rw [CongruenceSubgroup.strictPeriods_Gamma1]
  exact AddSubgroup.mem_zmultiples _

theorem periodic (f : CuspForm (Γ₁ℝ L) k) : Periodic (⇑f ∘ ofComplex) 1 :=
  SlashInvariantFormClass.periodic_comp_ofComplex f (one_mem_strictPeriods L)

theorem bdd (f : CuspForm (Γ₁ℝ L) k) : IsBoundedAtImInfty (⇑f) := by
  haveI : Fact (IsCusp OnePoint.infty (Γ₁ℝ L)) :=
    ⟨(Γ₁ℝ L).isCusp_of_mem_strictPeriods one_pos (one_mem_strictPeriods L)⟩
  exact ModularFormClass.bdd_at_infty f

theorem analytic (f : CuspForm (Γ₁ℝ L) k) : AnalyticAt ℂ (cuspFunction 1 (⇑f)) 0 :=
  analyticAt_cuspFunction_zero one_pos (periodic f) f.holo' (bdd f)

theorem qCoeff_zero_fun (n : ℕ) : qCoeff (0 : ℍ → ℂ) n = 0 := by
  rw [qCoeff, UpperHalfPlane.qExpansion_zero, map_zero]

theorem qCoeff_zero (n : ℕ) : qCoeff (⇑(0 : CuspForm (Γ₁ℝ L) k)) n = 0 := by
  rw [CuspForm.coe_zero, qCoeff_zero_fun]

theorem qCoeff_smul (c : ℂ) (f : CuspForm (Γ₁ℝ L) k) (n : ℕ) :
    qCoeff (⇑(c • f)) n = c * qCoeff (⇑f) n := by
  rw [qCoeff, qCoeff, CuspForm.IsGLPos.coe_smul, qExpansion_smul (analytic f), map_smul, smul_eq_mul]

theorem qCoeff_sub (f g : CuspForm (Γ₁ℝ L) k) (n : ℕ) :
    qCoeff (⇑(f - g)) n = qCoeff (⇑f) n - qCoeff (⇑g) n := by
  rw [qCoeff, qCoeff, qCoeff, CuspForm.coe_sub, qExpansion_sub (analytic f) (analytic g), map_sub]

end QCoeff

theorem apply_eq_zero_of_good {k : ℤ} (a : ℕ → ℂ) (e lam : ℕ → ℂ) (good : ℕ → Prop)
    (h1 : a 1 = 0)
    (heig : ∀ q : ℕ, q.Prime → good q → ∀ m : ℕ,
      a (q * m) + e q * (q : ℂ) ^ (k - 1) * (if q ∣ m then a (m / q) else 0) = lam q * a m) :
    ∀ n : ℕ, n ≠ 0 → (∀ q : ℕ, q.Prime → q ∣ n → good q) → a n = 0 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn0 hgood
    by_cases hn1 : n = 1
    · rw [hn1]; exact h1
    · set q := n.minFac with hq
      have hqp : q.Prime := Nat.minFac_prime hn1
      have hqn : q ∣ n := Nat.minFac_dvd n
      obtain ⟨m, hm⟩ := hqn
      have hm0 : m ≠ 0 := by rintro rfl; exact hn0 (by rw [hm, mul_zero])
      have hmlt : m < n := by
        rw [hm]
        exact lt_mul_left (Nat.pos_of_ne_zero hm0) hqp.one_lt
      have hgood_m : ∀ r : ℕ, r.Prime → r ∣ m → good r :=
        fun r hr hrm => hgood r hr (hm ▸ dvd_mul_of_dvd_right hrm q)
      have ham : a m = 0 := ih m hmlt hm0 hgood_m
      have hrel := heig q hqp (hgood q hqp ⟨m, hm⟩) m
      rw [ham, mul_zero] at hrel
      have hmid : (if q ∣ m then a (m / q) else 0) = 0 := by
        split_ifs with hqm
        · obtain ⟨r, hr⟩ := hqm
          have hr0 : r ≠ 0 := by rintro rfl; exact hm0 (by rw [hr, mul_zero])
          have hrlt : r < n := by
            calc r < m := by rw [hr]; exact lt_mul_left (Nat.pos_of_ne_zero hr0) hqp.one_lt
              _ < n := hmlt
          have hdiv : m / q = r := by rw [hr, Nat.mul_div_cancel_left _ hqp.pos]
          rw [hdiv]
          exact ih r hrlt hr0 (fun t ht htr => hgood_m t ht (hr ▸ dvd_mul_of_dvd_right htr q))
        · rfl
      rw [hmid, mul_zero, add_zero] at hrel
      rw [hm]
      exact hrel

theorem changeLevel_eq_of_forall_prime_notMem {M₁ M₂ N : ℕ} [NeZero N] (h₁ : M₁ ∣ N) (h₂ : M₂ ∣ N)
    (ε₁ : DirichletCharacter ℂ M₁) (ε₂ : DirichletCharacter ℂ M₂) (S : Finset ℕ)
    (hε : ∀ p : ℕ, p.Prime → p ∉ S → ε₁ (p : ZMod M₁) = ε₂ (p : ZMod M₂)) :
    DirichletCharacter.changeLevel h₁ ε₁ = DirichletCharacter.changeLevel h₂ ε₂ := by
  apply MulChar.ext'
  intro a
  by_cases ha : IsUnit a
  · obtain ⟨u, rfl⟩ := ha
    rw [DirichletCharacter.changeLevel_eq_cast_of_dvd ε₁ h₁ u,
      DirichletCharacter.changeLevel_eq_cast_of_dvd ε₂ h₂ u]
    obtain ⟨p, hpgt, hp, hpu⟩ :=
      Nat.forall_exists_prime_gt_and_eq_mod (Units.isUnit u) (S.sup id)
    have hpS : p ∉ S := by
      intro hpS
      have : p ≤ S.sup id := Finset.le_sup (f := id) hpS
      omega
    rw [← hpu, ZMod.cast_natCast h₁, ZMod.cast_natCast h₂]
    exact hε p hp hpS
  · rw [MulChar.map_nonunit _ ha, MulChar.map_nonunit _ ha]

theorem eq_of_forall_prime_notMem {M : ℕ} [NeZero M]
    (ε₁ ε₂ : DirichletCharacter ℂ M) (S : Finset ℕ)
    (hε : ∀ p : ℕ, p.Prime → p ∉ S → ε₁ (p : ZMod M) = ε₂ (p : ZMod M)) : ε₁ = ε₂ := by
  have h := changeLevel_eq_of_forall_prime_notMem (dvd_refl M) (dvd_refl M) ε₁ ε₂ S hε
  rwa [DirichletCharacter.changeLevel_self, DirichletCharacter.changeLevel_self] at h

theorem ne_zero_of_isEigenformWith {M : ℕ} {k : ℤ} {ε : DirichletCharacter ℂ M}
    {g : CuspForm (Γ₁ℝ M) k} (hg : CuspForm.IsEigenformWith ε g) : g ≠ 0 := by
  intro h0
  have h1 := hg.qCoeff_one
  rw [h0, qCoeff_zero] at h1
  exact zero_ne_one h1

theorem qCoeff_eq_of_level_eq
    {M : ℕ} [NeZero M] {k : ℤ}
    {ε₁ ε₂ : DirichletCharacter ℂ M}
    {g₁ g₂ : CuspForm (Γ₁ℝ M) k}
    (h₁ : CuspForm.IsPrimitiveForm ε₁ g₁) (h₂ : CuspForm.IsPrimitiveForm ε₂ g₂) (S : Finset ℕ)
    (ha : ∀ p : ℕ, p.Prime → p ∉ S → qCoeff g₁ p = qCoeff g₂ p)
    (hε : ∀ p : ℕ, p.Prime → p ∉ S → ε₁ (p : ZMod M) = ε₂ (p : ZMod M)) :
    ∀ n : ℕ, qCoeff g₁ n = qCoeff g₂ n := by
  have heq : ε₁ = ε₂ := eq_of_forall_prime_notMem ε₁ ε₂ S hε
  subst heq
  have hmo := CuspForm.eq_smul_of_isPrimitiveForm_of_qCoeff_hecke_eigen M k ε₁ g₁ h₁ g₂
    h₂.1.hasNebentypus S (fun p hp hpS hpM n => by
      rw [ha p hp hpS]
      exact h₂.1.hecke_of_not_dvd hp hpM n)
  rw [h₂.1.qCoeff_one, one_smul] at hmo
  intro n
  rw [hmo]

def LevelIH (k : ℤ) (L : ℕ) : Prop :=
  ∀ (N₁ N₂ : ℕ) (_ : NeZero N₁) (_ : NeZero N₂)
    (η₁ : DirichletCharacter ℂ N₁) (η₂ : DirichletCharacter ℂ N₂)
    (f₁ : CuspForm (Γ₁ℝ N₁) k) (f₂ : CuspForm (Γ₁ℝ N₂) k),
    CuspForm.IsPrimitiveForm η₁ f₁ → CuspForm.IsPrimitiveForm η₂ f₂ →
    ∀ S : Finset ℕ,
      (∀ p : ℕ, p.Prime → p ∉ S → qCoeff f₁ p = qCoeff f₂ p) →
      (∀ p : ℕ, p.Prime → p ∉ S → η₁ (p : ZMod N₁) = η₂ (p : ZMod N₂)) →
      Nat.lcm N₁ N₂ < L → N₁ = N₂

theorem qCoeff_eq_of_levelIH {k : ℤ} {L : ℕ} [NeZero L] (IH : LevelIH k L)
    {M₂ : ℕ} [NeZero M₂] {ε₂ : DirichletCharacter ℂ M₂} {g₂ : CuspForm (Γ₁ℝ M₂) k}
    (h₂ : CuspForm.IsPrimitiveForm ε₂ g₂) (hM₂L : M₂ ∣ L)
    (ε : DirichletCharacter ℂ L) (hε₂ : DirichletCharacter.changeLevel hM₂L ε₂ = ε)
    (S : Finset ℕ) (lam : ℕ → ℂ)
    (hlam : ∀ p : ℕ, p.Prime → p ∉ S → ¬ p ∣ L → qCoeff g₂ p = lam p)
    {N : ℕ} [NeZero N] {η : DirichletCharacter ℂ N} {h : CuspForm (Γ₁ℝ N) k}
    (hh : CuspForm.IsPrimitiveForm η h) (hNL : N ∣ L)
    (hη : DirichletCharacter.changeLevel hNL η = ε)
    (hpk : ∀ p : ℕ, p.Prime → p ∉ S → ¬ p ∣ L → qCoeff h p = lam p)
    (hlcm : Nat.lcm N M₂ < L) :
    N = M₂ ∧ ∀ r : ℕ, qCoeff h r = qCoeff g₂ r := by
  classical
  have hL0 : L ≠ 0 := NeZero.ne L
  have hcoef : ∀ p : ℕ, p.Prime → p ∉ S ∪ L.primeFactors → qCoeff h p = qCoeff g₂ p := by
    intro p hp hpS
    rw [Finset.mem_union, not_or] at hpS
    have hpL : ¬ p ∣ L := fun hd => hpS.2 (Nat.mem_primeFactors.2 ⟨hp, hd, hL0⟩)
    rw [hpk p hp hpS.1 hpL, hlam p hp hpS.1 hpL]
  have hchar : ∀ p : ℕ, p.Prime → p ∉ S ∪ L.primeFactors → η (p : ZMod N) = ε₂ (p : ZMod M₂) := by
    intro p hp hpS
    rw [Finset.mem_union, not_or] at hpS
    have hpL : ¬ p ∣ L := fun hd => hpS.2 (Nat.mem_primeFactors.2 ⟨hp, hd, hL0⟩)
    have hcop : Nat.Coprime p L := (Nat.Prime.coprime_iff_not_dvd hp).2 hpL
    rw [changeLevel_apply_natCast hNL η ε hη p hcop, changeLevel_apply_natCast hM₂L ε₂ ε hε₂ p hcop]
  have hNM : N = M₂ :=
    IH N M₂ inferInstance inferInstance η ε₂ h g₂ hh h₂ (S ∪ L.primeFactors) hcoef hchar hlcm
  subst hNM
  refine ⟨rfl, ?_⟩
  have hηε : η = ε₂ := DirichletCharacter.changeLevel_injective hNL (hη.trans hε₂.symm)
  subst hηε
  exact qCoeff_eq_of_level_eq hh h₂ (S ∪ L.primeFactors) hcoef hchar

theorem tower {k : ℤ} {L : ℕ} [NeZero L] (ε : DirichletCharacter ℂ L)
    (D : CuspForm (Γ₁ℝ L) k) (hD : CuspForm.HasNebentypus ε D)
    (S : Finset ℕ) (lam : ℕ → ℂ)
    (h1 : qCoeff (⇑D) 1 = 0)
    (heig : ∀ p : ℕ, p.Prime → p ∉ S → ¬ p ∣ L → ∀ n : ℕ,
      qCoeff (⇑D) (p * n) + ε (p : ZMod L) * (p : ℂ) ^ (k - 1) *
        (if p ∣ n then qCoeff (⇑D) (n / p) else 0) = lam p * qCoeff (⇑D) n)
    {q : ℕ} (hq : q.Prime) (hqL : q ∣ L) (L' : ℕ) (hL' : L = q ^ (L.factorization q) * L') :
    ∃ (n : ℕ) (d : Fin n → ℕ) (c : Fin n → ℂ) (N : Fin n → ℕ)
      (η : (i : Fin n) → DirichletCharacter ℂ (N i)) (h : (i : Fin n) → CuspForm (Γ₁ℝ (N i)) k),
      (∀ i, c i ≠ 0 →
        N i * d i ∣ L / q ∧ CuspForm.IsPrimitiveForm (η i) (h i) ∧
        (∃ hN : N i ∣ L, DirichletCharacter.changeLevel hN (η i) = ε) ∧
        ∀ p : ℕ, p.Prime → p ∉ S → ¬ p ∣ L → qCoeff (⇑(h i)) p = lam p) ∧
      ∀ m : ℕ, Nat.Coprime m L' →
        qCoeff (⇑D) m = ∑ i, c i * (if q * d i ∣ m then qCoeff (⇑(h i)) (m / (q * d i)) else 0) := by
  classical
  have hL0 : L ≠ 0 := NeZero.ne L
  have hL'L : L' ∣ L := Dvd.intro_left _ hL'.symm
  let echar : ℕ → ℂ := fun n => ε (n : ZMod L)
  let good : ℕ → Prop := fun p => p.Prime ∧ p ∉ S ∧ ¬ p ∣ L

  set K : ℕ := 2 * L * ∏ p ∈ S.filter Nat.Prime, p with hK
  have hK0 : K ≠ 0 := by
    rw [hK]
    refine mul_ne_zero (mul_ne_zero two_ne_zero hL0) ?_
    rw [Finset.prod_ne_zero_iff]
    intro p hp
    exact (Finset.mem_filter.1 hp).2.ne_zero
  have hvan : ∀ m : ℕ, Nat.Coprime m K → qCoeff (⇑D) m = 0 := by
    intro m hm
    have hm0 : m ≠ 0 := by
      rintro rfl
      rw [Nat.coprime_zero_left] at hm
      have h2 : 2 ∣ K := ⟨L * ∏ p ∈ S.filter Nat.Prime, p, by rw [hK]; ring⟩
      rw [hm] at h2
      exact absurd (Nat.le_of_dvd one_pos h2) (by norm_num)
    refine apply_eq_zero_of_good (k := k) (fun r => qCoeff (⇑D) r) echar lam good h1
      (fun p hp hg r => heig p hp hg.2.1 hg.2.2 r) m hm0 (fun p hp hpm => ⟨hp, ?_, ?_⟩)
    · intro hpS
      have hpK : p ∣ K := by
        rw [hK]
        exact dvd_mul_of_dvd_right (Finset.dvd_prod_of_mem _ (Finset.mem_filter.2 ⟨hpS, hp⟩)) _
      exact hp.one_lt.ne' ((hm.coprime_dvd_left hpm).eq_one_of_dvd hpK)
    · intro hpL
      have hpK : p ∣ K := by
        rw [hK]
        exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_right hpL 2) _
      exact hp.one_lt.ne' ((hm.coprime_dvd_left hpm).eq_one_of_dvd hpK)

  obtain ⟨F, hF, hFcoef⟩ :=
    CuspForm.exists_hasNebentypus_qCoeff_eq_sum_primeFactors_of_forall_coprime_qCoeff_eq_zero
      L k K hK0 ε D hD hvan
  have hqmem : q ∈ L.primeFactors := Nat.mem_primeFactors.2 ⟨hq, hqL, hL0⟩
  have hpL' : ∀ p ∈ L.primeFactors, p ≠ q → p ∣ L' := by
    intro p hp hpq
    have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
    have hpL : p ∣ L := Nat.dvd_of_mem_primeFactors hp
    have hcop : Nat.Coprime p (q ^ L.factorization q) :=
      Nat.Coprime.pow_right _ ((Nat.coprime_primes hpp hq).2 hpq)
    rw [hL'] at hpL
    exact hcop.dvd_of_dvd_mul_left hpL
  have hsingle : ∀ m : ℕ, Nat.Coprime m L' →
      qCoeff (⇑D) m = if q ∣ m then qCoeff (⇑(F q)) (m / q) else 0 := by
    intro m hm
    rw [hFcoef m, Finset.sum_eq_single q]
    · intro p hp hpq
      have hpm : ¬ p ∣ m := fun hd => by
        have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
        exact hpp.one_lt.ne' ((hm.coprime_dvd_left hd).eq_one_of_dvd (hpL' p hp hpq))
      rw [if_neg hpm]
    · intro hnot
      exact absurd hqmem hnot

  rcases hF q hqmem with hFq0 | ⟨εq, hεq, hFqneb⟩
  · refine ⟨0, Fin.elim0, Fin.elim0, Fin.elim0, fun i => Fin.elim0 i, fun i => Fin.elim0 i,
      fun i => Fin.elim0 i, fun m hm => ?_⟩
    rw [hsingle m hm, hFq0, Finset.univ_eq_empty, Finset.sum_empty]
    split_ifs
    · exact qCoeff_zero _
    · rfl
  · have hLq0 : L / q ≠ 0 :=
      (Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hL0) hqL) hq.pos).ne'
    haveI : NeZero (L / q) := ⟨hLq0⟩
    have hLqL : L / q ∣ L := Nat.div_dvd_of_dvd hqL
    obtain ⟨n, N, d, hNd, η, h, c, hprim, hsum⟩ :=
      CuspForm.exists_qCoeff_eq_sum_isPrimitiveForm_of_hasNebentypus (L / q) k εq (F q) hFqneb
    have hd0 : ∀ i, d i ≠ 0 := by
      intro i h0
      have := hNd i
      rw [h0, mul_zero] at this
      exact hLq0 (Nat.eq_zero_of_zero_dvd this)
    have hqd0 : ∀ i, q * d i ≠ 0 := fun i => mul_ne_zero hq.ne_zero (hd0 i)
    have hqdL : ∀ i, q * d i ∣ L := by
      intro i
      have hdi : d i ∣ L / q := Dvd.dvd.trans (Dvd.intro_left _ rfl) (hNd i)
      calc q * d i ∣ q * (L / q) := Nat.mul_dvd_mul_left q hdi
        _ = L := Nat.mul_div_cancel' hqL
    have hNL : ∀ i, N i ∣ L := fun i => (dvd_of_mul_right_dvd (hNd i)).trans hLqL
    have hηε : ∀ i, DirichletCharacter.changeLevel (hNL i) (η i) = ε := by
      intro i
      have e1 := DirichletCharacter.changeLevel_trans (η i) (dvd_of_mul_right_dvd (hNd i)) hLqL
      rw [(hprim i).2] at e1
      refine e1.trans ?_
      exact hεq

    have hstretch : ∀ m : ℕ, Nat.Coprime m L' →
        qCoeff (⇑D) m = ∑ i, c i * (if q * d i ∣ m then qCoeff (⇑(h i)) (m / (q * d i)) else 0) := by
      intro m hm
      rw [hsingle m hm]
      by_cases hqm : q ∣ m
      · obtain ⟨r, rfl⟩ := hqm
        rw [if_pos (dvd_mul_right q r), Nat.mul_div_cancel_left _ hq.pos, hsum r]
        refine Finset.sum_congr rfl fun i _ => ?_
        by_cases hdr : d i ∣ r
        · rw [if_pos hdr, if_pos (Nat.mul_dvd_mul_left q hdr), Nat.mul_div_mul_left _ _ hq.pos]
        · rw [if_neg hdr, if_neg (fun hd => hdr ((Nat.mul_dvd_mul_iff_left hq.pos).1 hd))]
      · rw [if_neg hqm]
        symm
        refine Finset.sum_eq_zero fun i _ => ?_
        rw [if_neg (fun hd => hqm (dvd_trans (Dvd.intro _ rfl) hd)), mul_zero]

    let 𝒯 : ℕ → (ℕ → ℂ) →ₗ[ℂ] (ℕ → ℂ) := fun p => if good p then heckeSeq k echar p else 0
    let v : Fin n → ℕ → ℂ := fun i => copSeq L' (stretchSeq (q * d i) (fun r => qCoeff (⇑(h i)) r))
    let β : Fin n → ℕ → ℂ := fun i p => if good p then qCoeff (⇑(h i)) p else 0
    let α : ℕ → ℂ := fun p => if good p then lam p else 0
    have hgoodL' : ∀ p, good p → Nat.Coprime p L' := fun p hg =>
      (Nat.Prime.coprime_iff_not_dvd hg.1).2 (fun hd => hg.2.2 (hd.trans hL'L))
    have hv : ∀ i ∈ (Finset.univ : Finset (Fin n)), ∀ p, 𝒯 p (v i) = β i p • v i := by
      intro i _ p
      by_cases hg : good p
      · simp only [𝒯, β, if_pos hg]
        have hp := hg.1
        have hpL := hg.2.2
        have hpN : ¬ p ∣ N i := fun hd => hpL (hd.trans (hNL i))
        have hcopqd : Nat.Coprime p (q * d i) :=
          (Nat.Prime.coprime_iff_not_dvd hp).2 (fun hd => hpL (hd.trans (hqdL i)))
        have hcopL : Nat.Coprime p L := (Nat.Prime.coprime_iff_not_dvd hp).2 hpL
        have hst : heckeSeq k echar p (stretchSeq (q * d i) (fun r => qCoeff (⇑(h i)) r)) =
            qCoeff (⇑(h i)) p • stretchSeq (q * d i) (fun r => qCoeff (⇑(h i)) r) :=
          heckeSeq_stretchSeq hp.ne_zero (hqd0 i) hcopqd (fun r => by
            have := (hprim i).1.1.hecke_of_not_dvd hp hpN r
            rw [changeLevel_apply_natCast (hNL i) (η i) ε (hηε i) p hcopL] at this
            exact this)
        show heckeSeq k echar p (copSeq L' _) = _
        rw [heckeSeq_copSeq hp.ne_zero (hgoodL' p hg), hst, copSeq_smul]
      · simp only [𝒯, β, if_neg hg, LinearMap.zero_apply, zero_smul]
    have haeig_fun : ∀ p, good p →
        heckeSeq k echar p (fun r => qCoeff (⇑D) r) = lam p • (fun r => qCoeff (⇑D) r) := by
      intro p hg
      funext r
      rw [heckeSeq_apply, Pi.smul_apply, smul_eq_mul]
      exact heig p hg.1 hg.2.1 hg.2.2 r
    have hw0 : (∑ i ∈ (Finset.univ : Finset (Fin n)), c i • v i) =
        copSeq L' (fun r => qCoeff (⇑D) r) := by
      funext r
      rw [Finset.sum_apply, copSeq_apply]
      by_cases hr : Nat.Coprime r L'
      · rw [if_pos hr, hstretch r hr]
        refine Finset.sum_congr rfl fun i _ => ?_
        simp only [Pi.smul_apply, smul_eq_mul, v, copSeq_apply, stretchSeq_apply, if_pos hr]
      · rw [if_neg hr]
        refine Finset.sum_eq_zero fun i _ => ?_
        simp only [Pi.smul_apply, smul_eq_mul, v, copSeq_apply, if_neg hr, mul_zero]
    have hw : ∀ p, 𝒯 p (∑ i ∈ (Finset.univ : Finset (Fin n)), c i • v i) =
        α p • ∑ i ∈ (Finset.univ : Finset (Fin n)), c i • v i := by
      intro p
      rw [hw0]
      by_cases hg : good p
      · simp only [𝒯, α, if_pos hg]
        rw [heckeSeq_copSeq hg.1.ne_zero (hgoodL' p hg), haeig_fun p hg, copSeq_smul]
      · simp only [𝒯, α, if_neg hg, LinearMap.zero_apply, zero_smul]
    obtain ⟨c', hc'β, hsum'⟩ := exists_coeff_restrict 𝒯 v β α Finset.univ c hv hw
    refine ⟨n, d, c', N, η, h, fun i hi => ⟨hNd i, (hprim i).1, ⟨hNL i, hηε i⟩,
      fun p hp hpS hpL => ?_⟩, fun m hm => ?_⟩
    · have hβ : β i = α := hc'β i (Finset.mem_univ i) hi
      have := congrFun hβ p
      simp only [β, α, if_pos (show good p from ⟨hp, hpS, hpL⟩)] at this
      exact this
    · have := congrFun hsum' m
      rw [hw0, copSeq_apply, if_pos hm] at this
      rw [this, Finset.sum_apply]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [Pi.smul_apply, smul_eq_mul, v, copSeq_apply, stretchSeq_apply, if_pos hm]

theorem keyStep {k : ℤ} {L : ℕ} (IH : LevelIH k L)
    {M₁ M₂ : ℕ} [NeZero M₁] [NeZero M₂]
    {ε₁ : DirichletCharacter ℂ M₁} {ε₂ : DirichletCharacter ℂ M₂}
    {g₁ : CuspForm (Γ₁ℝ M₁) k} {g₂ : CuspForm (Γ₁ℝ M₂) k}
    (h₁ : CuspForm.IsPrimitiveForm ε₁ g₁) (h₂ : CuspForm.IsPrimitiveForm ε₂ g₂) (S : Finset ℕ)
    (ha : ∀ p : ℕ, p.Prime → p ∉ S → qCoeff g₁ p = qCoeff g₂ p)
    (hε : ∀ p : ℕ, p.Prime → p ∉ S → ε₁ (p : ZMod M₁) = ε₂ (p : ZMod M₂))
    (hL : Nat.lcm M₁ M₂ = L) {q : ℕ} (hq : q.Prime)
    (hlt : M₂.factorization q < M₁.factorization q) : False := by
  classical
  have hM₁0 : M₁ ≠ 0 := NeZero.ne M₁
  have hM₂0 : M₂ ≠ 0 := NeZero.ne M₂
  have hL0 : L ≠ 0 := hL ▸ Nat.lcm_ne_zero hM₁0 hM₂0
  haveI : NeZero L := ⟨hL0⟩
  have hM₁L : M₁ ∣ L := hL ▸ Nat.dvd_lcm_left M₁ M₂
  have hM₂L : M₂ ∣ L := hL ▸ Nat.dvd_lcm_right M₁ M₂
  have hLprod : L ∣ M₁ * M₂ := hL ▸ Nat.lcm_dvd_mul M₁ M₂
  set m : ℕ := M₁.factorization q with hm_def
  set e : ℕ := M₂.factorization q with he_def
  have hm1 : 1 ≤ m := by omega
  have hqM₁ : q ∣ M₁ := (hq.dvd_iff_one_le_factorization hM₁0).2 hm1
  have hLfac : L.factorization q = m := by
    rw [← hL, Nat.factorization_lcm hM₁0 hM₂0, Finsupp.sup_apply]
    exact max_eq_left hlt.le
  have hqL : q ∣ L := hqM₁.trans hM₁L

  set L' : ℕ := L / q ^ L.factorization q with hL'_def
  have hLL' : L = q ^ L.factorization q * L' := (Nat.ordProj_mul_ordCompl_eq_self L q).symm
  have hqL' : Nat.Coprime q L' := Nat.coprime_ordCompl hq hL0
  have hL'L : L' ∣ L := Dvd.intro_left _ hLL'.symm
  have hL'0 : L' ≠ 0 := fun h0 => hL0 (by rw [hLL', h0, mul_zero])

  set ε : DirichletCharacter ℂ L := DirichletCharacter.changeLevel hM₁L ε₁ with hε_def
  have hε₁L : DirichletCharacter.changeLevel hM₁L ε₁ = ε := rfl
  have hε₂L : DirichletCharacter.changeLevel hM₂L ε₂ = ε :=
    (changeLevel_eq_of_forall_prime_notMem hM₁L hM₂L ε₁ ε₂ S hε).symm

  have hprod : DirichletCharacter.changeLevel (Nat.dvd_mul_right M₁ M₂) ε₁ =
      DirichletCharacter.changeLevel (Nat.dvd_mul_left M₂ M₁) ε₂ := by
    have e1 := DirichletCharacter.changeLevel_trans ε₁ hM₁L hLprod
    have e2 := DirichletCharacter.changeLevel_trans ε₂ hM₂L hLprod
    rw [hε₁L] at e1
    rw [hε₂L] at e2
    exact e1.trans e2.symm
  have hgcd : ε₁.FactorsThrough (M₁.gcd M₂) := DirichletCharacter.factorsThrough_gcd ε₁ ε₂ hprod
  have hMq0 : M₁ / q ≠ 0 :=
    (Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hM₁0) hqM₁) hq.pos).ne'
  have hgcd_dvd : M₁.gcd M₂ ∣ M₁ / q := by
    have hg0 : M₁.gcd M₂ ≠ 0 := Nat.gcd_ne_zero_left hM₁0
    rw [← Nat.factorization_le_iff_dvd hg0 hMq0, Nat.factorization_div hqM₁, hq.factorization,
      Finsupp.le_def]
    intro p
    rw [Finsupp.tsub_apply, Finsupp.single_apply]
    have hgM₁ : (M₁.gcd M₂).factorization p ≤ M₁.factorization p :=
      Finsupp.le_def.1 ((Nat.factorization_le_iff_dvd hg0 hM₁0).2 (Nat.gcd_dvd_left M₁ M₂)) p
    have hgM₂ : (M₁.gcd M₂).factorization p ≤ M₂.factorization p :=
      Finsupp.le_def.1 ((Nat.factorization_le_iff_dvd hg0 hM₂0).2 (Nat.gcd_dvd_right M₁ M₂)) p
    by_cases hpq : q = p
    · subst hpq
      rw [if_pos rfl]
      omega
    · rw [if_neg hpq]
      omega
  have hft : ε₁.FactorsThrough (M₁ / q) :=
    DirichletCharacter.FactorsThrough.mono ε₁ hgcd hgcd_dvd (Nat.div_dvd_of_dvd hqM₁)

  obtain ⟨G₁, -, hG₁c, hG₁n⟩ := CuspForm.exists_degeneracy_gamma1_hasNebentypus (k := k) (N := L)
    (d := 1) (show M₁ * 1 ∣ L by rw [mul_one]; exact hM₁L) g₁
  obtain ⟨G₂, -, hG₂c, hG₂n⟩ := CuspForm.exists_degeneracy_gamma1_hasNebentypus (k := k) (N := L)
    (d := 1) (show M₂ * 1 ∣ L by rw [mul_one]; exact hM₂L) g₂
  have hG₁c' : ∀ n, qCoeff (⇑G₁) n = qCoeff (⇑g₁) n := fun n => by
    rw [hG₁c n, if_pos (one_dvd n), Nat.div_one]
  have hG₂c' : ∀ n, qCoeff (⇑G₂) n = qCoeff (⇑g₂) n := fun n => by
    rw [hG₂c n, if_pos (one_dvd n), Nat.div_one]
  have hG₁neb : CuspForm.HasNebentypus ε G₁ := hG₁n ε₁ h₁.1.hasNebentypus
  have hG₂neb' : CuspForm.HasNebentypus (DirichletCharacter.changeLevel hM₂L ε₂) G₂ :=
    hG₂n ε₂ h₂.1.hasNebentypus
  have hG₂neb : CuspForm.HasNebentypus ε G₂ := by rw [hε₂L] at hG₂neb'; exact hG₂neb'
  set D : CuspForm (Γ₁ℝ L) k := G₁ - G₂ with hD_def
  have hDneb : CuspForm.HasNebentypus ε D := by
    intro γ hγ τ
    have e1 := hG₁neb γ hγ τ
    have e2 := hG₂neb γ hγ τ
    simp only [hD_def, CuspForm.coe_sub, Pi.sub_apply]
    rw [e1, e2]
    ring
  have hDc : ∀ n, qCoeff (⇑D) n = qCoeff (⇑g₁) n - qCoeff (⇑g₂) n := fun n => by
    rw [hD_def, qCoeff_sub, hG₁c', hG₂c']
  have hD1 : qCoeff (⇑D) 1 = 0 := by rw [hDc, h₁.1.qCoeff_one, h₂.1.qCoeff_one, sub_self]
  set lam : ℕ → ℂ := fun p => qCoeff (⇑g₁) p with hlam
  have heig : ∀ p : ℕ, p.Prime → p ∉ S → ¬ p ∣ L → ∀ n : ℕ,
      qCoeff (⇑D) (p * n) + ε (p : ZMod L) * (p : ℂ) ^ (k - 1) *
        (if p ∣ n then qCoeff (⇑D) (n / p) else 0) = lam p * qCoeff (⇑D) n := by
    intro p hp hpS hpL n
    have hpM₁ : ¬ p ∣ M₁ := fun hd => hpL (hd.trans hM₁L)
    have hpM₂ : ¬ p ∣ M₂ := fun hd => hpL (hd.trans hM₂L)
    have hcop : Nat.Coprime p L := (Nat.Prime.coprime_iff_not_dvd hp).2 hpL
    have r1 := h₁.1.hecke_of_not_dvd hp hpM₁ n
    have r2 := h₂.1.hecke_of_not_dvd hp hpM₂ n
    rw [changeLevel_apply_natCast hM₁L ε₁ ε hε₁L p hcop] at r1
    rw [changeLevel_apply_natCast hM₂L ε₂ ε hε₂L p hcop, ← ha p hp hpS] at r2
    simp only [hDc, hlam]
    have hite : (if p ∣ n then qCoeff (⇑g₁) (n / p) - qCoeff (⇑g₂) (n / p) else 0) =
        (if p ∣ n then qCoeff (⇑g₁) (n / p) else 0) -
          (if p ∣ n then qCoeff (⇑g₂) (n / p) else 0) := by
      split_ifs <;> ring
    rw [hite]
    linear_combination r1 - r2

  obtain ⟨n, d, c, N, η, h, hgood, htow⟩ := tower ε D hDneb S lam hD1 heig hq hqL L' hLL'
  have hlamg₂ : ∀ p : ℕ, p.Prime → p ∉ S → ¬ p ∣ L → qCoeff (⇑g₂) p = lam p :=
    fun p hp hpS _ => (ha p hp hpS).symm
  have hcopL : ∀ u : ℕ, Nat.Coprime u L → qCoeff (⇑g₁) u = qCoeff (⇑g₂) u := by
    intro u hu
    have huL' : Nat.Coprime u L' := Nat.Coprime.coprime_dvd_right hL'L hu
    have hqu : ¬ q ∣ u := fun hd =>
      hq.one_lt.ne' ((Nat.Coprime.coprime_dvd_left hd hu).eq_one_of_dvd hqL)
    have := htow u huL'
    rw [hDc] at this
    have hzero : ∑ i, c i * (if q * d i ∣ u then qCoeff (⇑(h i)) (u / (q * d i)) else 0) = 0 :=
      Finset.sum_eq_zero fun i _ => by
        rw [if_neg (fun hd => hqu ((Dvd.intro _ rfl : q ∣ q * d i).trans hd)), mul_zero]
    rw [hzero, sub_eq_zero] at this
    exact this
  rcases hm1.eq_or_lt with hm_one | hm_two
  ·
    have hm1' : m = 1 := hm_one.symm
    have hqM₂ : ¬ q ∣ M₂ := fun hd => by
      have := (hq.dvd_iff_one_le_factorization hM₂0).1 hd
      omega
    have hq2 : ¬ q ^ 2 ∣ M₁ := fun hd => by
      have := (hq.pow_dvd_iff_le_factorization hM₁0).1 hd
      omega
    have hLq : L = q * L' := by
      have := hLL'
      rw [hLfac, hm1', pow_one] at this
      exact this
    have hLdq : L / q = L' := by
      rw [hLq, Nat.mul_div_cancel_left _ hq.pos]
    have hM₂L' : M₂ ∣ L' := by
      have h1 : M₂ ∣ q * L' := hLq ▸ hM₂L
      exact (Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hq).2 hqM₂)).dvd_of_dvd_mul_left h1

    have hconst : ∀ i, c i ≠ 0 → d i = 1 → ∀ r, qCoeff (⇑(h i)) r = qCoeff (⇑g₂) r := by
      intro i hi hdi
      obtain ⟨hNd, hprim, ⟨hNL, hηε⟩, hpk⟩ := hgood i hi
      have hN0 : N i ≠ 0 := by
        intro h0
        rw [h0, zero_mul, hLdq] at hNd
        exact hL'0 (Nat.eq_zero_of_zero_dvd hNd)
      haveI : NeZero (N i) := ⟨hN0⟩
      have hNL' : N i ∣ L' := by
        have := dvd_of_mul_right_dvd hNd
        rwa [hLdq] at this
      have hlcm : Nat.lcm (N i) M₂ < L := by
        have hdvd : Nat.lcm (N i) M₂ ∣ L' := Nat.lcm_dvd hNL' hM₂L'
        calc Nat.lcm (N i) M₂ ≤ L' := Nat.le_of_dvd (Nat.pos_of_ne_zero hL'0) hdvd
          _ < L := by rw [hLq]; exact lt_mul_left (Nat.pos_of_ne_zero hL'0) hq.one_lt
      exact (qCoeff_eq_of_levelIH IH h₂ hM₂L ε hε₂L S lam hlamg₂ hprim hNL hηε hpk hlcm).2

    set a₁ : ℂ := qCoeff (⇑g₁) q with ha₁_def
    set b : ℂ := qCoeff (⇑g₂) q with hb_def
    set C : ℂ := ∑ i, (if d i = 1 then c i else 0) with hC
    have hcopq : Nat.Coprime q L' := hqL'
    have hcopqq : Nat.Coprime (q * q) L' := Nat.Coprime.mul_left hqL' hqL'
    have hterm1 : ∀ i, c i * (if q * d i ∣ q then qCoeff (⇑(h i)) (q / (q * d i)) else 0) =
        (if d i = 1 then c i else 0) := by
      intro i
      by_cases hci : c i = 0
      · rw [hci, zero_mul]
        split_ifs <;> rfl
      by_cases hdi : d i = 1
      · rw [hdi, mul_one, if_pos (dvd_refl q), Nat.div_self hq.pos, if_pos rfl,
          (hgood i hci).2.1.1.qCoeff_one, mul_one]
      · have hnd : ¬ q * d i ∣ q := fun hd =>
          hdi (Nat.dvd_one.1 ((Nat.mul_dvd_mul_iff_left hq.pos).1 (by rwa [mul_one])))
        rw [if_neg hnd, if_neg hdi, mul_zero]
    have hCq : qCoeff (⇑D) q = C := by
      rw [htow q hcopq, hC]
      exact Finset.sum_congr rfl fun i _ => hterm1 i
    have hterm2 : ∀ i,
        c i * (if q * d i ∣ q * q then qCoeff (⇑(h i)) (q * q / (q * d i)) else 0) =
          (if d i = 1 then c i else 0) * b := by
      intro i
      by_cases hci : c i = 0
      · rw [hci, zero_mul]
        split_ifs <;> simp
      by_cases hdi : d i = 1
      · rw [hdi, mul_one, if_pos (Dvd.intro q rfl), Nat.mul_div_cancel_left q hq.pos, if_pos rfl,
          hconst i hci hdi q]
      · have hnd : ¬ q * d i ∣ q * q := by
          intro hd
          have hdq : d i ∣ q := (Nat.mul_dvd_mul_iff_left hq.pos).1 hd
          rcases (Nat.dvd_prime hq).1 hdq with hd1 | hd2
          · exact hdi hd1
          · obtain ⟨hNd, -, -, -⟩ := hgood i hci
            rw [hLdq, hd2] at hNd
            exact hq.one_lt.ne' (hqL'.eq_one_of_dvd ((Dvd.intro_left _ rfl).trans hNd))
        rw [if_neg hnd, if_neg hdi, zero_mul, mul_zero]
    have hCqq : qCoeff (⇑D) (q * q) = C * b := by
      rw [htow (q * q) hcopqq, hC, Finset.sum_mul]
      exact Finset.sum_congr rfl fun i _ => hterm2 i
    have hread1 : a₁ - b = C := by rw [← hCq, hDc]
    have hread2 : qCoeff (⇑g₁) (q * q) - qCoeff (⇑g₂) (q * q) = C * b := by rw [← hCqq, hDc]
    have hU : qCoeff (⇑g₁) (q * q) = a₁ * a₁ := h₁.1.hecke_of_dvd hq hqM₁ q
    have hT : qCoeff (⇑g₂) (q * q) + ε₂ (q : ZMod M₂) * (q : ℂ) ^ (k - 1) = b * b := by
      have := h₂.1.hecke_of_not_dvd hq hqM₂ q
      rw [if_pos (dvd_refl q), Nat.div_self hq.pos, h₂.1.qCoeff_one, mul_one] at this
      exact this
    have hquad : a₁ * a₁ - a₁ * b + ε₂ (q : ZMod M₂) * (q : ℂ) ^ (k - 1) = 0 := by
      linear_combination -hU + hread2 + hT - b * hread1

    obtain ⟨hdvq, ε₁', hε₁'⟩ := hft
    have hε₁'v : ∀ u : ℕ, Nat.Coprime u M₁ → ε₁' (u : ZMod (M₁ / q)) = ε₁ (u : ZMod M₁) :=
      fun u hu => changeLevel_apply_natCast hdvq ε₁' ε₁ hε₁'.symm u hu
    have hg₁0 : g₁ ≠ 0 := ne_zero_of_isEigenformWith h₁.1
    have hneb₁ : CuspForm.HasNebentypus
        (DirichletCharacter.changeLevel (Nat.div_dvd_of_dvd hqM₁) ε₁') g₁ := by
      have := h₁.1.hasNebentypus
      rw [hε₁'] at this
      exact this
    have hdich :=
      CuspForm.qCoeff_sq_eq_mul_zpow_or_exists_hasNebentypus_qCoeff_hecke_eigen_of_dvd_of_not_sq_dvd
        M₁ k hq hqM₁ hq2 ε₁' g₁ hg₁0 hneb₁ (fun r => h₁.1.hecke_of_dvd hq hqM₁ r)
        (fun ℓ hℓ hℓM r => by
          have := h₁.1.hecke_of_not_dvd hℓ hℓM r
          rw [← hε₁'v ℓ ((Nat.Prime.coprime_iff_not_dvd hℓ).2 hℓM)] at this
          exact this)
    have hsq : a₁ ^ 2 = ε₁' (q : ZMod (M₁ / q)) * (q : ℂ) ^ (k - 2) := by
      rcases hdich with hsq | ⟨g, hg0, hgneb, hgT⟩
      · exact hsq
      · exfalso
        refine h₁.not_eigenpacketOccursAt (Nat.div_dvd_of_dvd hqM₁)
          (Nat.div_lt_self (Nat.pos_of_ne_zero hM₁0) hq.one_lt).ne
          ⟨ε₁', g, hg0, hgneb, M₁.primeFactors, fun p hp hpS => ?_⟩
        have hpM : ¬ p ∣ M₁ := fun hd => hpS (Nat.mem_primeFactors.2 ⟨hp, hd, hM₁0⟩)
        exact ⟨hε₁'v p ((Nat.Prime.coprime_iff_not_dvd hp).2 hpM), fun r => hgT p hp hpM r⟩

    have hqcopMq : Nat.Coprime q (M₁ / q) := (Nat.Prime.coprime_iff_not_dvd hq).2 (fun hd => hq2 (by
      have := Nat.mul_dvd_mul_left q hd
      rwa [Nat.mul_div_cancel' hqM₁, ← sq] at this))
    have hqcopM₂ : Nat.Coprime q M₂ := (Nat.Prime.coprime_iff_not_dvd hq).2 hqM₂
    have hcharq : ε₁' (q : ZMod (M₁ / q)) = ε₂ (q : ZMod M₂) := by
      set Q : ℕ := M₁ / q * M₂ with hQ
      haveI : NeZero Q := ⟨mul_ne_zero hMq0 hM₂0⟩
      have hqQ : Nat.Coprime q Q := Nat.Coprime.mul_right hqcopMq hqcopM₂
      obtain ⟨P, hPgt, hP, hPq⟩ :=
        Nat.forall_exists_prime_gt_and_eq_mod ((ZMod.isUnit_iff_coprime q Q).2 hqQ) L
      have hPL : ¬ P ∣ L := fun hd => (Nat.le_of_dvd (Nat.pos_of_ne_zero hL0) hd).not_gt hPgt
      have hd1 : M₁ / q ∣ Q := Dvd.intro _ rfl
      have hd2 : M₂ ∣ Q := Dvd.intro_left _ rfl
      have e1 : (P : ZMod (M₁ / q)) = (q : ZMod (M₁ / q)) := by
        have := congrArg (ZMod.castHom hd1 (ZMod (M₁ / q))) hPq
        rwa [map_natCast, map_natCast] at this
      have e2 : (P : ZMod M₂) = (q : ZMod M₂) := by
        have := congrArg (ZMod.castHom hd2 (ZMod M₂)) hPq
        rwa [map_natCast, map_natCast] at this
      have hPcopL : Nat.Coprime P L := (Nat.Prime.coprime_iff_not_dvd hP).2 hPL
      have hPcopM₁ : Nat.Coprime P M₁ := Nat.Coprime.coprime_dvd_right hM₁L hPcopL
      rw [← e1, ← e2, hε₁'v P hPcopM₁, changeLevel_apply_natCast hM₁L ε₁ ε hε₁L P hPcopL,
        ← changeLevel_apply_natCast hM₂L ε₂ ε hε₂L P hPcopL]
    have hq0 : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hq.ne_zero
    have hunit : IsUnit (ε₂ (q : ZMod M₂)) := by
      rw [← ZMod.coe_unitOfCoprime q hqcopM₂, ← MulChar.coe_toUnitHom]
      exact Units.isUnit _
    have hE : ε₂ (q : ZMod M₂) * (q : ℂ) ^ (k - 1) = (q : ℂ) * (a₁ * a₁) := by
      rw [← sq, hsq, hcharq, show (k - 1) = (k - 2) + 1 by ring, zpow_add_one₀ hq0]
      ring
    have ha0 : a₁ ≠ 0 := by
      intro h0
      have h2 : a₁ ^ 2 = 0 := by rw [h0]; ring
      rw [hsq, hcharq] at h2
      exact (mul_ne_zero hunit.ne_zero (zpow_ne_zero _ hq0)) h2
    have hbq : b = ((q : ℂ) + 1) * a₁ := by
      have h3 : a₁ * (((q : ℂ) + 1) * a₁ - b) = 0 := by
        linear_combination hquad - hE
      rcases mul_eq_zero.1 h3 with h4 | h4
      · exact absurd h4 ha0
      · exact (sub_eq_zero.1 h4).symm

    have hnormE : ‖ε₂ (q : ZMod M₂)‖ = 1 := by
      have := DirichletCharacter.unit_norm_eq_one ε₂ (ZMod.unitOfCoprime q hqcopM₂)
      rwa [ZMod.coe_unitOfCoprime] at this
    have hna : ‖a₁‖ ^ 2 = (q : ℝ) ^ (k - 2) := by
      rw [← norm_pow, hsq, hcharq, norm_mul, hnormE, one_mul, norm_zpow, Complex.norm_natCast]
    have hq1n : ‖((q : ℂ) + 1)‖ = (q : ℝ) + 1 := by
      rw [show ((q : ℂ) + 1) = ((q + 1 : ℕ) : ℂ) by push_cast; ring, Complex.norm_natCast]
      push_cast
      ring
    have hnb : ‖b‖ ^ 2 = ((q : ℝ) + 1) ^ 2 * (q : ℝ) ^ (k - 2) := by
      rw [hbq, norm_mul, mul_pow, hna, hq1n]
    have hHB := CuspForm.norm_sq_lt_of_hasNebentypus_qCoeff_hecke_eigen M₂ k ε₂ g₂
      (ne_zero_of_isEigenformWith h₂.1) h₂.1.hasNebentypus hq hqM₂ b
      (fun r => h₂.1.hecke_of_not_dvd hq hqM₂ r)
    rw [hnb] at hHB
    exact lt_irrefl _ hHB
  ·
    have hq2 : q ^ 2 ∣ M₁ := (hq.pow_dvd_iff_le_factorization hM₁0).2 (by omega)
    have hcop2 : ∀ u : ℕ, Nat.Coprime u M₁ → Nat.Coprime u M₂ → Nat.Coprime u L :=
      fun u hu1 hu2 => Nat.Coprime.coprime_dvd_right hLprod (Nat.Coprime.mul_right hu1 hu2)
    have hchild :=
      CuspForm.IsPrimitiveForm.pow_dvd_of_pow_dvd_of_sq_dvd_of_factorsThrough_of_forall_coprime_qCoeff_eq
        h₁ h₂ (fun u hu1 hu2 => hcopL u (hcop2 u hu1 hu2))
        (fun u hu1 hu2 => by
          have hcop := hcop2 u hu1 hu2
          rw [changeLevel_apply_natCast hM₁L ε₁ ε hε₁L u hcop,
            changeLevel_apply_natCast hM₂L ε₂ ε hε₂L u hcop])
        hq hq2 hft m (Nat.ordProj_dvd M₁ q)
    have hle : m ≤ e := (hq.pow_dvd_iff_le_factorization hM₂0).1 hchild
    omega

theorem level_eq_of_lcm_eq (k : ℤ) : ∀ (L : ℕ) {M₁ M₂ : ℕ} [NeZero M₁] [NeZero M₂]
    {ε₁ : DirichletCharacter ℂ M₁} {ε₂ : DirichletCharacter ℂ M₂}
    {g₁ : CuspForm (Γ₁ℝ M₁) k} {g₂ : CuspForm (Γ₁ℝ M₂) k},
    CuspForm.IsPrimitiveForm ε₁ g₁ → CuspForm.IsPrimitiveForm ε₂ g₂ → ∀ S : Finset ℕ,
    (∀ p : ℕ, p.Prime → p ∉ S → qCoeff g₁ p = qCoeff g₂ p) →
    (∀ p : ℕ, p.Prime → p ∉ S → ε₁ (p : ZMod M₁) = ε₂ (p : ZMod M₂)) →
    Nat.lcm M₁ M₂ = L → M₁ = M₂ := by
  intro L
  induction L using Nat.strong_induction_on with
  | _ L ih =>
    intro M₁ M₂ _ _ ε₁ ε₂ g₁ g₂ h₁ h₂ S ha hε hL
    have IH : LevelIH k L := by
      intro N₁ N₂ i₁ i₂ η₁ η₂ f₁ f₂ hf₁ hf₂ S' ha' hε' hlt
      haveI := i₁
      haveI := i₂
      exact ih (Nat.lcm N₁ N₂) hlt hf₁ hf₂ S' ha' hε' rfl
    by_contra hne
    have hM₁0 : M₁ ≠ 0 := NeZero.ne M₁
    have hM₂0 : M₂ ≠ 0 := NeZero.ne M₂
    obtain ⟨q, hq⟩ : ∃ q, M₁.factorization q ≠ M₂.factorization q := by
      by_contra hall
      push Not at hall
      exact hne (Nat.eq_of_factorization_eq hM₁0 hM₂0 hall)
    have hqprime : q.Prime := by
      by_contra hnp
      apply hq
      rw [Nat.factorization_eq_zero_of_not_prime _ hnp, Nat.factorization_eq_zero_of_not_prime _ hnp]
    rcases lt_or_gt_of_ne hq with hlt | hlt
    · exact keyStep IH h₂ h₁ S (fun p hp hpS => (ha p hp hpS).symm)
        (fun p hp hpS => (hε p hp hpS).symm) (by rw [Nat.lcm_comm]; exact hL) hqprime hlt
    · exact keyStep IH h₁ h₂ S ha hε hL hqprime hlt

end SMOGamma1

end

theorem solution
    {M₁ M₂ : ℕ} [NeZero M₁] [NeZero M₂] {k : ℤ}
    {ε₁ : DirichletCharacter ℂ M₁} {ε₂ : DirichletCharacter ℂ M₂}
    {g₁ : CuspForm (CongruenceSubgroup.Gamma1 M₁) k}
    {g₂ : CuspForm (CongruenceSubgroup.Gamma1 M₂) k}
    (h₁ : CuspForm.IsPrimitiveForm ε₁ g₁) (h₂ : CuspForm.IsPrimitiveForm ε₂ g₂) (S : Finset ℕ)
    (ha : ∀ p : ℕ, p.Prime → p ∉ S → ModularFormClass.qCoeff g₁ p = ModularFormClass.qCoeff g₂ p)
    (hε : ∀ p : ℕ, p.Prime → p ∉ S → ε₁ (p : ZMod M₁) = ε₂ (p : ZMod M₂)) :
    M₁ = M₂ ∧ ∀ n : ℕ, ModularFormClass.qCoeff g₁ n = ModularFormClass.qCoeff g₂ n := by
  have hM : M₁ = M₂ := SMOGamma1.level_eq_of_lcm_eq k (Nat.lcm M₁ M₂) h₁ h₂ S ha hε rfl
  subst hM
  exact ⟨rfl, SMOGamma1.qCoeff_eq_of_level_eq h₁ h₂ S ha hε⟩

end S_CuspForm_IsPrimitiveForm_level_eq_and_qCoeff_eq_of_forall_prime_notMem_qCoeff_eq
end P2MW
export P2MW.S_CuspForm_IsPrimitiveForm_level_eq_and_qCoeff_eq_of_forall_prime_notMem_qCoeff_eq (solution)
