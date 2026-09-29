-- Prove2me | solution 1 for CuspForm.IsEigenformWith.exists_isPrimitiveForm_sq_sub_mul_add_eq_zero_of_eigenpacketOccursAt_div
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/6bf83c52-b3bf-5a28-bcce-77482f4638e6

import Mathlib
import Definitions.Def_FLTPrelim_Modularity
import Definitions.Def_CuspForm_PrimitiveFormGamma1
import Theorems.Thm_CuspForm_exists_qCoeff_eq_sum_isPrimitiveForm_of_hasNebentypus
import Theorems.Thm_CuspForm_exists_isPrimitiveForm_of_hasNebentypus_qCoeff_hecke_eigen
import Theorems.Thm_CuspForm_IsPrimitiveForm_level_eq_and_qCoeff_eq_of_forall_prime_notMem_qCoeff_eq
import Theorems.Thm_CuspForm_IsEigenformWith_dvd_and_qCoeff_eq_or_not_dvd_and_qCoeff_sq_sub_eq_zero_of_isPrimitiveForm_of_not_sq_dvd
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CuspForm_IsEigenformWith_exists_isPrimitiveForm_sq_sub_mul_add_eq_zero_of_eigenpacketOccursAt_div
p2m_attr_erase "instance" "FLT.HyperbolicMeasure.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatIntUpperHalfPlaneVolume_definitions FLT.HyperbolicMeasure.instIsOpenPosMeasureUpperHalfPlaneVolume_definitions FLT.Gamma0FundamentalSet.instContinuousConstSMulSpecialLinearGroupFinOfNatNatIntUpperHalfPlane_definitions FLT.L2ProductionInstance.isFiniteMeasure_gamma0 FLT.L2ProductionInstance.countable_SL2Z FLT.L2ProductionInstance.countable_quotient FLT.L2ProductionInstance.nontrivial_gamma0L2 Ihara.instGroupIharaAmalgam"
p2m_attr_erase "simp" "ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL FLT.TruncatedDomainPartition.unipotentDiagonalSum_zero Ihara.wConj_coe Ihara.wConj_symm_coe Ihara.coe_iota1 Ihara.coe_iota1SL Ihara.iota1Mat_apply_one_zero Ihara.iota1Mat_apply_zero_zero Ihara.iota1Mat_apply_zero_one Ihara.iota1Mat_apply_one_one Ihara.coe_iota0 Ihara.iharaEdge_one Ihara.pairFamily_zero Ihara.iharaEdge_zero Ihara.pairFamily_one Ihara.coe_amalgamToGamma0Away Ihara.coe_vertexZero Ihara.coe_slToAway FreyPackage.ModMCarrier.coe_rescaleLin_apply ModularForm.AtkinLehnerDatum.mk.injEq ModularForm.AtkinLehnerDatum.alGL_coe ModularForm.AtkinLehnerDatum.mk.sizeOf_spec ModularForm.AtkinLehnerDatum.sqUnitSL_coe ModularForm.AtkinLehnerDatum.det_sqUnit ModularForm.AtkinLehnerDatum.det_mat CuspForm.PeterssonCoset.mapGL_apply"

set_option autoImplicit false

open CongruenceSubgroup ModularFormClass
open scoped MatrixGroups

noncomputable section

namespace OldAtQPrimitive

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

theorem apply_natCast_eq_of_forall_prime {M N : ℕ} (hN1 : N ≠ 1) (εM : DirichletCharacter ℂ M)
    (ε : DirichletCharacter ℂ N)
    (h : ∀ p : ℕ, p.Prime → ¬ p ∣ N → εM (p : ZMod M) = ε (p : ZMod N)) :
    ∀ n : ℕ, Nat.Coprime n N → εM (n : ZMod M) = ε (n : ZMod N) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn
    rcases Nat.lt_or_ge n 2 with hlt | hge
    · interval_cases n
      ·
        exact absurd (Nat.coprime_zero_left N |>.mp hn) hN1
      · simp
    ·
      have hn1 : n ≠ 1 := by omega
      set p := n.minFac with hpdef
      have hp : p.Prime := Nat.minFac_prime hn1
      obtain ⟨m, hm⟩ : p ∣ n := Nat.minFac_dvd n
      have hm0 : m ≠ 0 := by
        rintro rfl
        rw [mul_zero] at hm
        omega
      have hmlt : m < n := by
        rw [hm]
        exact lt_mul_of_one_lt_left (Nat.pos_of_ne_zero hm0) hp.one_lt
      have hpN : ¬ p ∣ N := by
        intro hpN
        have h1 : p ∣ Nat.gcd n N := Nat.dvd_gcd ⟨m, hm⟩ hpN
        rw [hn] at h1
        exact hp.one_lt.ne' (Nat.dvd_one.mp h1)
      have hmN : Nat.Coprime m N := Nat.Coprime.coprime_dvd_left ⟨p, by rw [hm]; ring⟩ hn
      rw [hm, Nat.cast_mul, Nat.cast_mul, map_mul, map_mul, h p hp hpN, ih m hmlt hmN]

theorem changeLevel_eq_of_forall_prime {M N : ℕ} [NeZero N] (hMN : M ∣ N)
    (εM : DirichletCharacter ℂ M) (ε : DirichletCharacter ℂ N)
    (h : ∀ p : ℕ, p.Prime → ¬ p ∣ N → εM (p : ZMod M) = ε (p : ZMod N)) :
    DirichletCharacter.changeLevel hMN εM = ε := by
  haveI : NeZero M := ⟨fun h0 => by
    subst h0
    exact (NeZero.ne N) (Nat.eq_zero_of_zero_dvd hMN)⟩
  apply MulChar.ext'
  intro a
  by_cases ha : IsUnit a
  · obtain ⟨u, rfl⟩ := ha
    rw [DirichletCharacter.changeLevel_eq_cast_of_dvd εM hMN u]

    set n : ℕ := (u : ZMod N).val with hndef
    have hnu : (n : ZMod N) = (u : ZMod N) := ZMod.natCast_zmod_val _
    have hncop : Nat.Coprime n N := ZMod.val_coe_unit_coprime u
    by_cases hN1 : N = 1
    ·
      subst hN1
      have hM1 : M = 1 := Nat.dvd_one.mp hMN
      subst hM1
      have h1 : (ZMod.cast (u : ZMod 1) : ZMod 1) = 1 := Subsingleton.elim _ _
      have h2 : ((u : ZMod 1)) = 1 := Subsingleton.elim _ _
      rw [h1, h2, map_one, map_one]
    · rw [← hnu, ZMod.cast_natCast hMN]
      exact apply_natCast_eq_of_forall_prime hN1 εM ε h n hncop
  · rw [MulChar.map_nonunit _ ha, MulChar.map_nonunit]

    exact ha

theorem one_mem_strictPeriods (N : ℕ) :
    (1 : ℝ) ∈ ((Gamma1 N : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by
  rw [CongruenceSubgroup.strictPeriods_Gamma1]
  exact AddSubgroup.mem_zmultiples _

theorem eq_zero_of_forall_qCoeff_eq_zero {N : ℕ} {k : ℤ} (f : CuspForm (Gamma1 N) k)
    (h : ∀ n : ℕ, qCoeff f n = 0) : f = 0 := by
  have hΓ := one_mem_strictPeriods N
  haveI : Fact (IsCusp OnePoint.infty
      ((Gamma1 N : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))) :=
    ⟨Subgroup.isCusp_of_mem_strictPeriods one_pos hΓ⟩
  have hq : UpperHalfPlane.qExpansion 1 (⇑f) = 0 := by
    ext n
    simpa [qCoeff] using h n
  have hcoe : (⇑f : UpperHalfPlane → ℂ) = 0 :=
    (UpperHalfPlane.qExpansion_eq_zero_iff one_pos
      (SlashInvariantFormClass.periodic_comp_ofComplex f hΓ) (ModularFormClass.holo f)
      (ModularFormClass.bdd_at_infty f)).mp hq
  exact DFunLike.ext f 0 fun τ => by simpa using congrFun hcoe τ

theorem exists_isPrimitiveForm_of_eigen_notMem
    (N : ℕ) [NeZero N] (k : ℤ) (ε : DirichletCharacter ℂ N) (f : CuspForm (Gamma1 N) k) (hf0 : f ≠ 0)
    (hε : CuspForm.HasNebentypus ε f) (S : Finset ℕ) (lam : ℕ → ℂ)
    (hf : ∀ p : ℕ, p.Prime → p ∉ S → ¬ p ∣ N → ∀ n : ℕ,
        qCoeff f (p * n) +
            ε (p : ZMod N) * (p : ℂ) ^ (k - 1) * (if p ∣ n then qCoeff f (n / p) else 0) =
          lam p * qCoeff f n) :
    ∃ (M : ℕ) (_ : NeZero M) (εM : DirichletCharacter ℂ M) (g : CuspForm (Gamma1 M) k),
      M ∣ N ∧ CuspForm.IsPrimitiveForm εM g ∧
      ∀ p : ℕ, p.Prime → p ∉ S → ¬ p ∣ N →
        qCoeff g p = lam p ∧ εM (p : ZMod M) = ε (p : ZMod N) := by
  classical
  obtain ⟨n, M, d, hMd, εM, g, c, hprim, hdec⟩ :=
    CuspForm.exists_qCoeff_eq_sum_isPrimitiveForm_of_hasNebentypus N k ε f hε
  set e : ℕ → ℂ := fun m => ε (m : ZMod N) with he
  let T : ℕ → (ℕ → ℂ) →ₗ[ℂ] (ℕ → ℂ) := fun p => heckeSeq k e p
  let a : ℕ → ℂ := fun m => qCoeff f m
  let v : Fin n → (ℕ → ℂ) := fun i => stretchSeq (d i) (fun m => qCoeff (g i) m)
  let good : ℕ → Prop := fun p => p.Prime ∧ p ∉ S ∧ ¬ p ∣ N
  let α : ℕ → ℂ := fun p => if good p then lam p else 0
  let β : Fin n → ℕ → ℂ := fun i p => if good p then qCoeff (g i) p else 0
  let T' : ℕ → (ℕ → ℂ) →ₗ[ℂ] (ℕ → ℂ) := fun p => if good p then T p else 0
  have hM_dvd : ∀ i, M i ∣ N := fun i => dvd_of_mul_right_dvd (hMd i)
  have hd_dvd : ∀ i, d i ∣ N := fun i => dvd_of_mul_left_dvd (hMd i)
  have hd_ne : ∀ i, d i ≠ 0 := fun i h0 => (NeZero.ne N) (Nat.eq_zero_of_zero_dvd (h0 ▸ hd_dvd i))
  have hM_ne : ∀ i, M i ≠ 0 := fun i h0 => (NeZero.ne N) (Nat.eq_zero_of_zero_dvd (h0 ▸ hM_dvd i))
  have ha_sum : (∑ i ∈ Finset.univ, c i • v i) = a := by
    funext m
    rw [Finset.sum_apply]
    simp only [Pi.smul_apply, smul_eq_mul, v, stretchSeq_apply, a]
    exact (hdec m).symm
  have hv : ∀ i ∈ (Finset.univ : Finset (Fin n)), ∀ p, T' p (v i) = β i p • v i := by
    intro i _ p
    by_cases hg : good p
    · simp only [T', β, if_pos hg]
      obtain ⟨hp, -, hpN⟩ := hg
      have hpM : ¬ p ∣ M i := fun h => hpN (dvd_trans h (hM_dvd i))
      have hpd : Nat.Coprime p (d i) :=
        (Nat.Prime.coprime_iff_not_dvd hp).mpr fun h => hpN (dvd_trans h (hd_dvd i))
      have hpcop : Nat.Coprime p N := (Nat.Prime.coprime_iff_not_dvd hp).mpr hpN
      have hεi : εM i (p : ZMod (M i)) = ε (p : ZMod N) :=
        changeLevel_apply_natCast (hM_dvd i) (εM i) ε (hprim i).2 p hpcop
      refine heckeSeq_stretchSeq hp.ne_zero (hd_ne i) hpd fun m => ?_
      have h := (hprim i).1.isEigenformWith.hecke_of_not_dvd hp hpM m
      rw [hεi] at h
      exact h
    · simp only [T', β, if_neg hg, LinearMap.zero_apply, zero_smul]
  have ha : ∀ p, T' p a = α p • a := by
    intro p
    by_cases hg : good p
    · simp only [T', α, if_pos hg]
      obtain ⟨hp, hpS, hpN⟩ := hg
      funext m
      rw [Pi.smul_apply, smul_eq_mul]
      change heckeSeq k e p a m = _
      rw [heckeSeq_apply]
      exact hf p hp hpS hpN m
    · simp only [T', α, if_neg hg, LinearMap.zero_apply, zero_smul]
  have hw : ∀ p, T' p (∑ i ∈ Finset.univ, c i • v i) = α p • ∑ i ∈ Finset.univ, c i • v i := by
    intro p; rw [ha_sum]; exact ha p
  have hne : (∑ i ∈ Finset.univ, c i • v i) ≠ 0 := by
    rw [ha_sum]
    intro h0
    exact hf0 (eq_zero_of_forall_qCoeff_eq_zero f fun m => congrFun h0 m)
  obtain ⟨i, -, hi⟩ := exists_packet_eq T' v β α Finset.univ c hv hw hne
  haveI : NeZero (M i) := ⟨hM_ne i⟩
  refine ⟨M i, ⟨hM_ne i⟩, εM i, g i, hM_dvd i, (hprim i).1, fun p hp hpS hpN => ⟨?_, ?_⟩⟩
  · have h := hi p
    simp only [β, α, if_pos (show good p from ⟨hp, hpS, hpN⟩)] at h
    exact h
  · have hpcop : Nat.Coprime p N := (Nat.Prime.coprime_iff_not_dvd hp).mpr hpN
    exact changeLevel_apply_natCast (hM_dvd i) (εM i) ε (hprim i).2 p hpcop

theorem main
    {M : ℕ} [NeZero M] {k : ℤ} {ε : DirichletCharacter ℂ M}
    {h : CuspForm (Gamma1 M) k} (hh : CuspForm.IsEigenformWith ε h)
    (q : ℕ) (hq : q.Prime) (hqM : q ∣ M) (hq2 : ¬ q ^ 2 ∣ M)
    (hold : CuspForm.EigenpacketOccursAt k (fun n => qCoeff h n) (fun n => ε (n : ZMod M)) (M / q)) :
    ∃ (Mg : ℕ) (_ : NeZero Mg) (εg : DirichletCharacter ℂ Mg)
      (g : CuspForm (Gamma1 Mg) k) (hMg : Mg ∣ M / q),
      CuspForm.IsPrimitiveForm εg g ∧
      DirichletCharacter.changeLevel (hMg.trans (Nat.div_dvd_of_dvd hqM)) εg = ε ∧
      (∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ M → qCoeff g ℓ = qCoeff h ℓ) ∧
      qCoeff h q ^ 2 - qCoeff g q * qCoeff h q + εg (q : ZMod Mg) * (q : ℂ) ^ (k - 1) = 0 := by
  classical
  have hM0 : M ≠ 0 := NeZero.ne M

  have hh0 : h ≠ 0 := by
    intro h0
    have h1 := hh.qCoeff_one
    rw [h0] at h1
    have : qCoeff (⇑(0 : CuspForm (Gamma1 M) k)) 1 = 0 := by
      rw [CuspForm.coe_zero, qCoeff, UpperHalfPlane.qExpansion_zero, map_zero]
    rw [this] at h1
    exact zero_ne_one h1

  obtain ⟨Mg, instMg, εg, g, hMgM, hprim, hpk⟩ :=
    CuspForm.exists_isPrimitiveForm_of_hasNebentypus_qCoeff_hecke_eigen M k ε h hh0 hh.hasNebentypus
      (fun p => qCoeff h p) (fun p hp hpM n => hh.hecke_of_not_dvd hp hpM n)

  have hchange : DirichletCharacter.changeLevel hMgM εg = ε :=
    changeLevel_eq_of_forall_prime hMgM εg ε fun p hp hpM => (hpk p hp hpM).2

  have hMq_pos : M / q ≠ 0 := by
    intro h0
    rcases (Nat.div_eq_zero_iff).mp h0 with h1 | h1
    · exact hq.ne_zero h1
    · exact absurd (Nat.le_of_dvd (Nat.pos_of_ne_zero hM0) hqM) (not_le.mpr h1)
  haveI : NeZero (M / q) := ⟨hMq_pos⟩
  have hMq_dvd : M / q ∣ M := Nat.div_dvd_of_dvd hqM
  have hq_ndvd : ¬ q ∣ M / q := by
    intro hqd
    apply hq2
    have : q * q ∣ q * (M / q) := Nat.mul_dvd_mul_left q hqd
    rw [Nat.mul_div_cancel' hqM] at this
    simpa [pow_two] using this
  obtain ⟨ε', h', hh'0, hneb', S, hS⟩ := hold
  obtain ⟨M', instM', εg', g', hM'q, hprim', hpk'⟩ :=
    exists_isPrimitiveForm_of_eigen_notMem (M / q) k ε' h' hh'0 hneb' S (fun p => qCoeff h p)
      (fun p hp hpS _hpMq n => (hS p hp hpS).2 n)

  have hSMO := CuspForm.IsPrimitiveForm.level_eq_and_qCoeff_eq_of_forall_prime_notMem_qCoeff_eq
    hprim hprim' (S ∪ M.primeFactors)
    (fun p hp hpS => by
      rw [Finset.mem_union, not_or] at hpS
      have hpM : ¬ p ∣ M := fun hd => hpS.2 (Nat.mem_primeFactors.mpr ⟨hp, hd, hM0⟩)
      have hpMq : ¬ p ∣ M / q := fun hd => hpM (dvd_trans hd hMq_dvd)
      rw [(hpk p hp hpM).1, (hpk' p hp hpS.1 hpMq).1])
    (fun p hp hpS => by
      rw [Finset.mem_union, not_or] at hpS
      have hpM : ¬ p ∣ M := fun hd => hpS.2 (Nat.mem_primeFactors.mpr ⟨hp, hd, hM0⟩)
      have hpMq : ¬ p ∣ M / q := fun hd => hpM (dvd_trans hd hMq_dvd)
      rw [(hpk p hp hpM).2, (hpk' p hp hpS.1 hpMq).2, (hS p hp hpS.1).1])
  have hMg_eq : Mg = M' := hSMO.1
  have hMgq : Mg ∣ M / q := hMg_eq ▸ hM'q
  have hq_ndvd_Mg : ¬ q ∣ Mg := fun hd => hq_ndvd (dvd_trans hd hMgq)

  have hdich :=
    CuspForm.IsEigenformWith.dvd_and_qCoeff_eq_or_not_dvd_and_qCoeff_sq_sub_eq_zero_of_isPrimitiveForm_of_not_sq_dvd
      hh hprim hMgM hchange (fun ℓ hℓ hℓM => (hpk ℓ hℓ hℓM).1) q hq hqM hq2
  have hquad : qCoeff h q ^ 2 - qCoeff g q * qCoeff h q +
      εg (q : ZMod Mg) * (q : ℂ) ^ (k - 1) = 0 := by
    rcases hdich with ⟨hqMg, -⟩ | ⟨-, hquad⟩
    · exact absurd hqMg hq_ndvd_Mg
    · exact hquad
  refine ⟨Mg, instMg, εg, g, hMgq, hprim, ?_, fun ℓ hℓ hℓM => (hpk ℓ hℓ hℓM).1, hquad⟩

  exact hchange

end OldAtQPrimitive

end

theorem solution
    {M : ℕ} [NeZero M] {k : ℤ} {ε : DirichletCharacter ℂ M}
    {h : CuspForm (CongruenceSubgroup.Gamma1 M) k} (hh : CuspForm.IsEigenformWith ε h)
    (q : ℕ) (hq : q.Prime) (hqM : q ∣ M) (hq2 : ¬ q ^ 2 ∣ M)
    (hold : CuspForm.EigenpacketOccursAt k (fun n => ModularFormClass.qCoeff h n)
      (fun n => ε (n : ZMod M)) (M / q)) :
    ∃ (Mg : ℕ) (_ : NeZero Mg) (εg : DirichletCharacter ℂ Mg)
      (g : CuspForm (CongruenceSubgroup.Gamma1 Mg) k) (hMg : Mg ∣ M / q),
      CuspForm.IsPrimitiveForm εg g ∧
      DirichletCharacter.changeLevel (hMg.trans (Nat.div_dvd_of_dvd hqM)) εg = ε ∧
      (∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ M → ModularFormClass.qCoeff g ℓ = ModularFormClass.qCoeff h ℓ) ∧
      ModularFormClass.qCoeff h q ^ 2 - ModularFormClass.qCoeff g q * ModularFormClass.qCoeff h q +
        εg (q : ZMod Mg) * (q : ℂ) ^ (k - 1) = 0 :=
  OldAtQPrimitive.main hh q hq hqM hq2 hold

end S_CuspForm_IsEigenformWith_exists_isPrimitiveForm_sq_sub_mul_add_eq_zero_of_eigenpacketOccursAt_div
end P2MW
export P2MW.S_CuspForm_IsEigenformWith_exists_isPrimitiveForm_sq_sub_mul_add_eq_zero_of_eigenpacketOccursAt_div (solution)
