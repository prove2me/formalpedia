-- Prove2me | solution 1 for CuspForm.eq_smul_of_isPrimitiveForm_of_qCoeff_hecke_eigen
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/0c13b72b-3b38-5999-8f76-b5b7106a236c

import Mathlib
import Definitions.Def_FLTPrelim_Modularity
import Definitions.Def_CuspForm_PrimitiveFormGamma1
import Theorems.Thm_CuspForm_exists_basis_hasNebentypus_qCoeff_hecke_eigen
import Theorems.Thm_CuspForm_exists_hasNebentypus_qCoeff_eq_sum_primeFactors_of_forall_coprime_qCoeff_eq_zero
import Theorems.Thm_CuspForm_HasNebentypus_sum_filter_eq_of_sum_eq
import Theorems.Thm_UpperHalfPlane_eq_of_forall_qCoeff_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CuspForm_eq_smul_of_isPrimitiveForm_of_qCoeff_hecke_eigen
p2m_attr_erase "instance" "FLT.HyperbolicMeasure.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatIntUpperHalfPlaneVolume_definitions FLT.HyperbolicMeasure.instIsOpenPosMeasureUpperHalfPlaneVolume_definitions FLT.Gamma0FundamentalSet.instContinuousConstSMulSpecialLinearGroupFinOfNatNatIntUpperHalfPlane_definitions FLT.L2ProductionInstance.isFiniteMeasure_gamma0 FLT.L2ProductionInstance.countable_SL2Z FLT.L2ProductionInstance.countable_quotient FLT.L2ProductionInstance.nontrivial_gamma0L2 Ihara.instGroupIharaAmalgam"
p2m_attr_erase "simp" "FLT.TruncatedDomainPartition.unipotentDiagonalSum_zero Ihara.wConj_coe Ihara.wConj_symm_coe Ihara.coe_iota1 Ihara.coe_iota1SL Ihara.iota1Mat_apply_one_zero Ihara.iota1Mat_apply_zero_zero Ihara.iota1Mat_apply_zero_one Ihara.iota1Mat_apply_one_one Ihara.coe_iota0 Ihara.iharaEdge_one Ihara.pairFamily_zero Ihara.iharaEdge_zero Ihara.pairFamily_one Ihara.coe_amalgamToGamma0Away Ihara.coe_vertexZero Ihara.coe_slToAway FreyPackage.ModMCarrier.coe_rescaleLin_apply ModularForm.AtkinLehnerDatum.mk.injEq ModularForm.AtkinLehnerDatum.alGL_coe ModularForm.AtkinLehnerDatum.mk.sizeOf_spec ModularForm.AtkinLehnerDatum.sqUnitSL_coe ModularForm.AtkinLehnerDatum.det_sqUnit ModularForm.AtkinLehnerDatum.det_mat"

set_option autoImplicit false
set_option maxHeartbeats 3200000

open CongruenceSubgroup ModularFormClass UpperHalfPlane Function
open scoped MatrixGroups

noncomputable section

namespace MultOnePrimitive

local notation "Γ₁ℝ" M => ((Gamma1 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))

theorem exists_packet_eq {K V P ι : Type*} [Field K] [AddCommGroup V] [Module K V]
    (T : P → V →ₗ[K] V) (v : ι → V) (β : ι → P → K) (α : P → K) (s : Finset ι) :
    ∀ c : ι → K,
      (∀ i ∈ s, ∀ p, T p (v i) = β i p • v i) →
      (∀ p, T p (∑ i ∈ s, c i • v i) = α p • ∑ i ∈ s, c i • v i) →
      (∑ i ∈ s, c i • v i ≠ 0) →
      ∃ i ∈ s, ∀ p, β i p = α p := by
  classical
  induction s using Finset.strongInduction with
  | H s ih =>
    intro c hv hw hne
    by_cases hall : ∃ i ∈ s, ∀ p, β i p = α p
    · exact hall
    push Not at hall
    have hsne : s.Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]
      rintro rfl
      exact hne (by simp)
    obtain ⟨j, hj⟩ := hsne
    obtain ⟨p₀, hp₀⟩ := hall j hj
    set w : V := ∑ i ∈ s, c i • v i with hwdef
    set c' : ι → K := fun i => c i * (β i p₀ - β j p₀) with hc'
    have hsum : ∑ i ∈ s, c' i • v i = (α p₀ - β j p₀) • w := by
      have h2 : ∑ i ∈ s, c' i • v i = T p₀ w - β j p₀ • w := by
        rw [hwdef, map_sum, Finset.smul_sum, ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun i hi => ?_
        rw [map_smul, hv i hi p₀, smul_smul, smul_smul, ← sub_smul, hc']
        congr 1
        ring
      rw [h2, hw p₀, sub_smul]
    have herase : ∑ i ∈ s.erase j, c' i • v i = ∑ i ∈ s, c' i • v i := by
      apply Finset.sum_erase
      rw [hc']
      simp
    have hne' : ∑ i ∈ s.erase j, c' i • v i ≠ 0 := by
      rw [herase, hsum]
      exact smul_ne_zero (sub_ne_zero.mpr (Ne.symm hp₀)) hne
    have heig' : ∀ p, T p (∑ i ∈ s.erase j, c' i • v i) = α p • ∑ i ∈ s.erase j, c' i • v i := by
      intro p
      rw [herase, hsum, map_smul, hw p, smul_comm]
    obtain ⟨i, hi, hβ⟩ := ih (s.erase j) (Finset.erase_ssubset hj) c'
      (fun i hi p => hv i (Finset.mem_of_mem_erase hi) p) heig' hne'
    exact ⟨i, Finset.mem_of_mem_erase hi, hβ⟩

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

theorem eq_of_qCoeff_eq (f₁ f₂ : CuspForm (Γ₁ℝ L) k) (h : ∀ n : ℕ, qCoeff f₁ n = qCoeff f₂ n) :
    f₁ = f₂ :=
  DFunLike.ext' (UpperHalfPlane.eq_of_forall_qCoeff_eq (periodic f₁) f₁.holo' (bdd f₁)
    (periodic f₂) f₂.holo' (bdd f₂) h)

theorem qCoeff_zero_fun (n : ℕ) : qCoeff (0 : ℍ → ℂ) n = 0 := by
  rw [qCoeff, UpperHalfPlane.qExpansion_zero, map_zero]

theorem qCoeff_zero (n : ℕ) : qCoeff (⇑(0 : CuspForm (Γ₁ℝ L) k)) n = 0 := by
  rw [CuspForm.coe_zero, qCoeff_zero_fun]

theorem qCoeff_add (f₁ f₂ : CuspForm (Γ₁ℝ L) k) (n : ℕ) :
    qCoeff (⇑(f₁ + f₂)) n = qCoeff (⇑f₁) n + qCoeff (⇑f₂) n := by
  rw [qCoeff, qCoeff, qCoeff, CuspForm.coe_add, qExpansion_add (analytic f₁) (analytic f₂), map_add]

theorem qCoeff_smul (c : ℂ) (f : CuspForm (Γ₁ℝ L) k) (n : ℕ) :
    qCoeff (⇑(c • f)) n = c * qCoeff (⇑f) n := by
  rw [qCoeff, qCoeff, CuspForm.IsGLPos.coe_smul, qExpansion_smul (analytic f), map_smul, smul_eq_mul]

theorem qCoeff_sub_smul (f g : CuspForm (Γ₁ℝ L) k) (c : ℂ) (n : ℕ) :
    qCoeff (⇑(f - c • g)) n = qCoeff (⇑f) n - c * qCoeff (⇑g) n := by
  have hcg : AnalyticAt ℂ (cuspFunction 1 (c • (⇑g : ℍ → ℂ))) 0 := analytic (c • g)
  rw [qCoeff, qCoeff, qCoeff, CuspForm.coe_sub, CuspForm.IsGLPos.coe_smul,
    qExpansion_sub (analytic f) hcg, map_sub, qExpansion_smul (analytic g), map_smul, smul_eq_mul]

theorem qCoeff_sum {ι : Type*} (s : Finset ι) (c : ι → ℂ) (f : ι → CuspForm (Γ₁ℝ L) k) (n : ℕ) :
    qCoeff (⇑(∑ i ∈ s, c i • f i)) n = ∑ i ∈ s, c i * qCoeff (⇑(f i)) n := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty, Finset.sum_empty, qCoeff_zero]
  | insert j s hj ih => rw [Finset.sum_insert hj, Finset.sum_insert hj, qCoeff_add, qCoeff_smul, ih]

end QCoeff

theorem hasNebentypus_sub_smul {L : ℕ} {k : ℤ} {ε : DirichletCharacter ℂ L}
    {f g : CuspForm (Γ₁ℝ L) k} (hf : CuspForm.HasNebentypus ε f) (hg : CuspForm.HasNebentypus ε g)
    (c : ℂ) : CuspForm.HasNebentypus ε (f - c • g) := by
  intro γ hγ τ
  have h1 := hf γ hγ τ
  have h2 := hg γ hγ τ
  simp only [CuspForm.coe_sub, CuspForm.IsGLPos.coe_smul, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  rw [h1, h2]
  ring

theorem hasNebentypus_smul {L : ℕ} {k : ℤ} {ε : DirichletCharacter ℂ L}
    {g : CuspForm (Γ₁ℝ L) k} (hg : CuspForm.HasNebentypus ε g) (c : ℂ) :
    CuspForm.HasNebentypus ε (c • g) := by
  intro γ hγ τ
  have h2 := hg γ hγ τ
  simp only [CuspForm.IsGLPos.coe_smul, Pi.smul_apply, smul_eq_mul]
  rw [h2]
  ring

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

section PerPrime

variable {M : ℕ} [NeZero M] {k : ℤ}

theorem perPrime (ε : DirichletCharacter ℂ M) (g : CuspForm (Γ₁ℝ M) k)
    (hg : CuspForm.IsPrimitiveForm ε g) (S : Finset ℕ)
    (p : ℕ) (hp : p ∈ M.primeFactors) (G : CuspForm (Γ₁ℝ (M / p)) k)
    (hG : G = 0 ∨ ∃ εp : DirichletCharacter ℂ (M / p),
      DirichletCharacter.changeLevel (Nat.div_dvd_of_dvd (Nat.dvd_of_mem_primeFactors hp)) εp = ε ∧
        CuspForm.HasNebentypus εp G) :
    ∃ (n : ℕ) (v : Fin n → ℕ → ℂ) (lam : Fin n → ℕ → ℂ) (c : Fin n → ℂ) (s : Finset (Fin n)),
      (∀ i ∈ s, ∀ q : ℕ, q.Prime → ¬ q ∣ M →
        heckeSeq k (fun m => ε (m : ZMod M)) q (v i) = lam i q • v i) ∧
      (∀ i ∈ s, ¬ ∀ q : ℕ, q.Prime → q ∉ S → ¬ q ∣ M → lam i q = qCoeff (⇑g) q) ∧
      (∀ n : ℕ, (if p ∣ n then qCoeff (⇑G) (n / p) else 0) = ∑ i ∈ s, c i * v i n) := by
  classical
  have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
  have hpM : p ∣ M := Nat.dvd_of_mem_primeFactors hp
  have hM0 : M ≠ 0 := NeZero.ne M
  have hLdvd : M / p ∣ M := Nat.div_dvd_of_dvd hpM
  have hL0 : M / p ≠ 0 := by
    intro h0
    exact hM0 (Nat.eq_zero_of_zero_dvd (h0 ▸ hLdvd))
  have hLne : M / p ≠ M := by
    intro hLM
    have : M / p < M := Nat.div_lt_self (Nat.pos_of_ne_zero hM0) hpp.one_lt
    rw [hLM] at this
    exact lt_irrefl _ this
  haveI : NeZero (M / p) := ⟨hL0⟩
  rcases hG with hG0 | ⟨εp, hεp, hGneb⟩
  ·
    refine ⟨0, Fin.elim0, Fin.elim0, Fin.elim0, ∅, by simp, by simp, fun n => ?_⟩
    rw [hG0, Finset.sum_empty]
    split_ifs
    · exact qCoeff_zero _
    · rfl
  ·
    obtain ⟨n, bs, hbs⟩ := CuspForm.exists_basis_hasNebentypus_qCoeff_hecke_eigen (M / p) k
    choose χ hχ hlam using hbs

    let lam : Fin n → ℕ → ℂ := fun i q =>
      if h : q.Prime ∧ ¬ q ∣ M / p then Classical.choose (hlam i q h.1 h.2) else 0
    have hlam_spec : ∀ i (q : ℕ) (hq : q.Prime) (hqL : ¬ q ∣ M / p), ∀ m : ℕ,
        qCoeff (⇑(bs i)) (q * m) + χ i (q : ZMod (M / p)) * (q : ℂ) ^ (k - 1) *
          (if q ∣ m then qCoeff (⇑(bs i)) (m / q) else 0) = lam i q * qCoeff (⇑(bs i)) m := by
      intro i q hq hqL m
      have : lam i q = Classical.choose (hlam i q hq hqL) := by
        simp only [lam, dif_pos (show q.Prime ∧ ¬ q ∣ M / p from ⟨hq, hqL⟩)]
      rw [this]
      exact Classical.choose_spec (hlam i q hq hqL) m

    set c : Fin n → ℂ := fun i => bs.repr G i with hc
    have hsum0 : ∑ i ∈ (Finset.univ : Finset (Fin n)), c i • bs i = G := by
      rw [hc]; exact bs.sum_repr G
    have hproj := CuspForm.HasNebentypus.sum_filter_eq_of_sum_eq (Finset.univ : Finset (Fin n)) χ
      (fun i => c i • bs i) (fun i _ => hasNebentypus_smul (hχ i) (c i)) hGneb hsum0
    set s := (Finset.univ : Finset (Fin n)).filter (fun i => χ i = εp) with hs
    let v : Fin n → ℕ → ℂ := fun i => stretchSeq p (fun m => qCoeff (⇑(bs i)) m)
    refine ⟨n, v, lam, c, s, ?_, ?_, ?_⟩
    ·
      intro i hi q hq hqM
      have hχi : χ i = εp := (Finset.mem_filter.1 hi).2
      have hqL : ¬ q ∣ M / p := fun h => hqM (dvd_trans h hLdvd)
      have hqcop : Nat.Coprime q M := (Nat.Prime.coprime_iff_not_dvd hq).mpr hqM
      have hqp : Nat.Coprime q p :=
        (Nat.coprime_primes hq hpp).2 (fun h => hqM (h ▸ hpM))
      have hεq : χ i (q : ZMod (M / p)) = ε (q : ZMod M) := by
        rw [hχi]; exact changeLevel_apply_natCast hLdvd εp ε hεp q hqcop
      refine heckeSeq_stretchSeq hq.ne_zero hpp.ne_zero hqp (fun m => ?_)
      have := hlam_spec i q hq hqL m
      rw [hεq] at this
      exact this
    ·
      intro i hi hall
      have hχi : χ i = εp := (Finset.mem_filter.1 hi).2
      apply hg.not_eigenpacketOccursAt hLdvd hLne
      refine ⟨χ i, bs i, bs.ne_zero i, hχ i, S ∪ M.primeFactors, fun q hq hqS => ?_⟩
      rw [Finset.mem_union, not_or] at hqS
      have hqM : ¬ q ∣ M := fun h => hqS.2 (Nat.mem_primeFactors.2 ⟨hq, h, hM0⟩)
      have hqL : ¬ q ∣ M / p := fun h => hqM (dvd_trans h hLdvd)
      have hqcop : Nat.Coprime q M := (Nat.Prime.coprime_iff_not_dvd hq).mpr hqM
      have hεq : χ i (q : ZMod (M / p)) = ε (q : ZMod M) := by
        rw [hχi]; exact changeLevel_apply_natCast hLdvd εp ε hεp q hqcop
      refine ⟨hεq, fun m => ?_⟩
      have := hlam_spec i q hq hqL m
      rw [hall q hq hqS.1 hqM] at this
      exact this
    ·
      intro m
      have hcoef : ∀ r : ℕ, qCoeff (⇑G) r = ∑ i ∈ s, c i * qCoeff (⇑(bs i)) r := by
        intro r
        rw [← qCoeff_sum s c bs r, hproj]
      simp only [v, stretchSeq_apply]
      split_ifs with hpm
      · rw [hcoef]
      · simp

end PerPrime

section Main

variable {M : ℕ} [NeZero M] {k : ℤ}

theorem main (ε : DirichletCharacter ℂ M) (g : CuspForm (Γ₁ℝ M) k)
    (hg : CuspForm.IsPrimitiveForm ε g) (f : CuspForm (Γ₁ℝ M) k)
    (hf : CuspForm.HasNebentypus ε f) (S : Finset ℕ)
    (hfS : ∀ p : ℕ, p.Prime → p ∉ S → ¬ p ∣ M → ∀ n : ℕ,
        qCoeff (⇑f) (p * n) + ε (p : ZMod M) * (p : ℂ) ^ (k - 1) *
          (if p ∣ n then qCoeff (⇑f) (n / p) else 0) = qCoeff (⇑g) p * qCoeff (⇑f) n) :
    f = qCoeff (⇑f) 1 • g := by
  classical
  have hM0 : M ≠ 0 := NeZero.ne M
  have heig := hg.isEigenformWith
  set e : ℕ → ℂ := fun m => ε (m : ZMod M) with he
  set b : ℕ → ℂ := fun m => qCoeff (⇑g) m with hb

  set f' : CuspForm (Γ₁ℝ M) k := f - qCoeff (⇑f) 1 • g with hf'
  have hf'neb : CuspForm.HasNebentypus ε f' := hasNebentypus_sub_smul hf heig.hasNebentypus _
  set a : ℕ → ℂ := fun m => qCoeff (⇑f') m with ha
  have ha_apply : ∀ m, a m = qCoeff (⇑f) m - qCoeff (⇑f) 1 * qCoeff (⇑g) m := fun m =>
    qCoeff_sub_smul f g _ m
  have ha1 : a 1 = 0 := by rw [ha_apply, heig.qCoeff_one, mul_one, sub_self]
  let good : ℕ → Prop := fun q => q.Prime ∧ q ∉ S ∧ ¬ q ∣ M
  have haeig : ∀ q : ℕ, q.Prime → good q → ∀ m : ℕ,
      a (q * m) + e q * (q : ℂ) ^ (k - 1) * (if q ∣ m then a (m / q) else 0) = b q * a m := by
    intro q hq hgq m
    have h1 := hfS q hq hgq.2.1 hgq.2.2 m
    have h2 := heig.hecke_of_not_dvd hq hgq.2.2 m
    simp only [ha_apply, hb, he]
    have hite : (if q ∣ m then qCoeff (⇑f) (m / q) - qCoeff (⇑f) 1 * qCoeff (⇑g) (m / q) else 0) =
        (if q ∣ m then qCoeff (⇑f) (m / q) else 0) -
          qCoeff (⇑f) 1 * (if q ∣ m then qCoeff (⇑g) (m / q) else 0) := by
      split_ifs <;> ring
    rw [hite]
    linear_combination h1 - qCoeff (⇑f) 1 * h2

  set K : ℕ := 2 * M * ∏ q ∈ S.filter Nat.Prime, q with hK
  have hK0 : K ≠ 0 := by
    rw [hK]
    refine mul_ne_zero (mul_ne_zero two_ne_zero hM0) ?_
    rw [Finset.prod_ne_zero_iff]
    intro q hq
    exact (Nat.prime_of_mem_primeFactors (by
      have := (Finset.mem_filter.1 hq).2
      exact Nat.mem_primeFactors.2 ⟨this, dvd_refl q, this.ne_zero⟩)).ne_zero
  have hvan : ∀ m : ℕ, Nat.Coprime m K → a m = 0 := by
    intro m hm
    have hm0 : m ≠ 0 := by
      rintro rfl
      rw [Nat.coprime_zero_left] at hm
      have h2 : 2 ∣ K := ⟨M * ∏ q ∈ S.filter Nat.Prime, q, by rw [hK]; ring⟩
      rw [hm] at h2
      exact absurd (Nat.le_of_dvd one_pos h2) (by norm_num)
    refine apply_eq_zero_of_good (k := k) a e b good ha1 haeig m hm0 (fun q hq hqm => ⟨hq, ?_, ?_⟩)
    · intro hqS
      have hqK : q ∣ K := by
        rw [hK]
        exact dvd_mul_of_dvd_right (Finset.dvd_prod_of_mem _ (Finset.mem_filter.2 ⟨hqS, hq⟩)) _
      exact hq.one_lt.ne' ((hm.coprime_dvd_left hqm).eq_one_of_dvd hqK)
    · intro hqM
      have hqK : q ∣ K := by
        rw [hK]
        exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_right hqM 2) _
      exact hq.one_lt.ne' ((hm.coprime_dvd_left hqm).eq_one_of_dvd hqK)

  obtain ⟨G, hG, hGcoef⟩ :=
    CuspForm.exists_hasNebentypus_qCoeff_eq_sum_primeFactors_of_forall_coprime_qCoeff_eq_zero
      M k K hK0 ε f' hf'neb hvan

  have hall : ∀ p : ℕ, ∃ (n : ℕ) (v : Fin n → ℕ → ℂ) (lam : Fin n → ℕ → ℂ) (c : Fin n → ℂ)
      (s : Finset (Fin n)), p ∈ M.primeFactors →
      (∀ i ∈ s, ∀ q : ℕ, q.Prime → ¬ q ∣ M → heckeSeq k e q (v i) = lam i q • v i) ∧
      (∀ i ∈ s, ¬ ∀ q : ℕ, q.Prime → q ∉ S → ¬ q ∣ M → lam i q = qCoeff (⇑g) q) ∧
      (∀ n : ℕ, (if p ∣ n then qCoeff (⇑(G p)) (n / p) else 0) = ∑ i ∈ s, c i * v i n) := by
    intro p
    by_cases hp : p ∈ M.primeFactors
    · obtain ⟨n, v, lam, c, s, h1, h2, h3⟩ := perPrime ε g hg S p hp (G p) (hG p hp)
      exact ⟨n, v, lam, c, s, fun _ => ⟨h1, h2, h3⟩⟩
    · exact ⟨0, Fin.elim0, Fin.elim0, Fin.elim0, ∅, fun h => absurd h hp⟩
  choose n v lam c s hpk using hall

  set T : Finset (Σ p : ℕ, Fin (n p)) := M.primeFactors.sigma s with hT
  let V : (Σ p : ℕ, Fin (n p)) → ℕ → ℂ := fun x => v x.1 x.2
  let C : (Σ p : ℕ, Fin (n p)) → ℂ := fun x => c x.1 x.2
  let 𝒯 : ℕ → (ℕ → ℂ) →ₗ[ℂ] (ℕ → ℂ) := fun q => if good q then heckeSeq k e q else 0
  let β : (Σ p : ℕ, Fin (n p)) → ℕ → ℂ := fun x q => if good q then lam x.1 x.2 q else 0
  let α : ℕ → ℂ := fun q => if good q then b q else 0
  have ha_sum : (∑ x ∈ T, C x • V x) = a := by
    funext m
    rw [Finset.sum_apply, hT, Finset.sum_sigma]
    simp only [Pi.smul_apply, smul_eq_mul, V, C]
    rw [ha]
    simp only
    rw [hGcoef m]
    exact Finset.sum_congr rfl (fun p hp => ((hpk p hp).2.2 m).symm)
  have hv : ∀ x ∈ T, ∀ q, 𝒯 q (V x) = β x q • V x := by
    intro x hx q
    obtain ⟨hp, hi⟩ := Finset.mem_sigma.1 hx
    by_cases hgq : good q
    · simp only [𝒯, β, if_pos hgq]
      exact (hpk x.1 hp).1 x.2 hi q hgq.1 hgq.2.2
    · simp only [𝒯, β, if_neg hgq, LinearMap.zero_apply, zero_smul]
  have haT : ∀ q, 𝒯 q a = α q • a := by
    intro q
    by_cases hgq : good q
    · simp only [𝒯, α, if_pos hgq]
      funext m
      rw [Pi.smul_apply, smul_eq_mul, heckeSeq_apply]
      exact haeig q hgq.1 hgq m
    · simp only [𝒯, α, if_neg hgq, LinearMap.zero_apply, zero_smul]

  have ha0 : a = 0 := by
    by_contra hne
    have hw : ∀ q, 𝒯 q (∑ x ∈ T, C x • V x) = α q • ∑ x ∈ T, C x • V x := by
      intro q; rw [ha_sum]; exact haT q
    have hne' : (∑ x ∈ T, C x • V x) ≠ 0 := by rwa [ha_sum]
    obtain ⟨x, hx, hxβ⟩ := exists_packet_eq 𝒯 V β α T C hv hw hne'
    obtain ⟨hp, hi⟩ := Finset.mem_sigma.1 hx
    apply (hpk x.1 hp).2.1 x.2 hi
    intro q hq hqS hqM
    have := hxβ q
    simp only [β, α, if_pos (show good q from ⟨hq, hqS, hqM⟩)] at this
    exact this

  have hf'0 : f' = 0 := by
    apply eq_of_qCoeff_eq
    intro m
    rw [qCoeff_zero]
    exact congrFun ha0 m
  rw [hf', sub_eq_zero] at hf'0
  exact hf'0

end Main

end MultOnePrimitive

end

open scoped MatrixGroups in
theorem solution
    (M : ℕ) [NeZero M] (k : ℤ) (ε : DirichletCharacter ℂ M) (g : CuspForm (Gamma1 M) k)
    (hg : CuspForm.IsPrimitiveForm ε g) (f : CuspForm (Gamma1 M) k)
    (hf : CuspForm.HasNebentypus ε f) (S : Finset ℕ)
    (hfS : ∀ p : ℕ, p.Prime → p ∉ S → ¬ p ∣ M → ∀ n : ℕ,
        ModularFormClass.qCoeff f (p * n) +
            ε (p : ZMod M) * (p : ℂ) ^ (k - 1) *
              (if p ∣ n then ModularFormClass.qCoeff f (n / p) else 0) =
          ModularFormClass.qCoeff g p * ModularFormClass.qCoeff f n) :
    f = ModularFormClass.qCoeff f 1 • g :=
  MultOnePrimitive.main ε g hg f hf S hfS

end S_CuspForm_eq_smul_of_isPrimitiveForm_of_qCoeff_hecke_eigen
end P2MW
export P2MW.S_CuspForm_eq_smul_of_isPrimitiveForm_of_qCoeff_hecke_eigen (solution)
