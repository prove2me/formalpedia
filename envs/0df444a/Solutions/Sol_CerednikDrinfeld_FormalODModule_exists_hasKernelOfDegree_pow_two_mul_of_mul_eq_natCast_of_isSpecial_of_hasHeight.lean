-- Prove2me | solution 1 for CerednikDrinfeld.FormalODModule.exists_hasKernelOfDegree_pow_two_mul_of_mul_eq_natCast_of_isSpecial_of_hasHeight
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/58396686-7115-5c80-bb79-f0a0a6ae12ca

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Theorems.Thm_CerednikDrinfeld_FormalODModule_HasKernelOfDegree_comp
import Theorems.Thm_CerednikDrinfeld_FormalODModule_exists_X_pow_mem_span_of_hasKernelOfDegree
import Theorems.Thm_CerednikDrinfeld_FormalODModule_exists_hasKernelOfDegree_of_X_pow_mem_span_of_field
import Theorems.Thm_CerednikDrinfeld_FormalODModule_exists_X_pow_mem_span_of_X_pow_mem_span_comp
import Theorems.Thm_CerednikDrinfeld_SpecialFormalODModule_even_of_isIsogenyOfHeight_of_isAlgClosed
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_FormalODModule_exists_hasKernelOfDegree_pow_two_mul_of_mul_eq_natCast_of_isSpecial_of_hasHeight
p2m_attr_erase "instance" "instTopologicallyFGOfFiniteType MvFormalGroup.CartierModule.instAddCommGroup MvFormalGroup.CartierModule.instNeg MvFormalGroup.CartierModule.instAdd MvFormalGroup.CartierModule.instZero MvFormalGroup.WittLaw.instTendstoCofiniteProdMk MvFormalGroup.CartierModule.instModuleWittVector"
p2m_attr_erase "simp" "MvFormalGroup.CartierModule.toPowerSeries_sub MvFormalGroup.WittLaw.verFam_zero MvFormalGroup.WittLaw.verFam_succ MvFormalGroup.CartierModule.toPowerSeries_frobenius MvFormalGroup.CartierModule.toPowerSeries_verschiebung MvFormalGroup.WittLaw.blk_apply MvFormalGroup.WittLaw.weight_apply MvFormalGroup.CartierModule.toPowerSeries_map MvFormalGroup.CartierModule.toPowerSeries_precompFun MvFormalGroup.CartierModule.toPowerSeries_mapFun MvFormalGroup.CartierModule.mk.injEq MvFormalGroup.WittLaw.pairFam_apply MvFormalGroup.CartierModule.endAct_apply MvFormalGroup.WittLaw.frobFam_apply MvFormalGroup.CartierModule.toPowerSeries_zero MvFormalGroup.CartierModule.tangent_apply MvFormalGroup.CartierModule.toPowerSeries_precomp MvFormalGroup.CartierModule.Examples.toPowerSeries_addLinear MvFormalGroup.CartierModule.toPowerSeries_add MvFormalGroup.CartierModule.toPowerSeries_neg MvFormalGroup.CartierModule.mk.sizeOf_spec MvFormalGroup.CartierModule.inBlk_apply MvFormalGroup.WittLaw.teichFam_apply MvFormalGroup.CartierModule.toPowerSeries_homothety MvFormalGroup.WittLaw.verPoly_succ MvFormalGroup.WittLaw.xVec_coeff MvFormalGroup.WittLaw.cVec_coeff MvFormalGroup.WittLaw.cVec_mul MvFormalGroup.WittLaw.mulFam_apply MvFormalGroup.CartierModule.mapLinear_apply MvFormalGroup.WittLaw.cVec_add MvFormalGroup.WittLaw.cVec_zero MvFormalGroup.WittLaw.verPoly_zero MvFormalGroup.CartierModule.toPowerSeries_wittSMul MvFormalGroup.CartierModule.toPowerSeries_smul_witt MvFormalGroup.WittLaw.cVec_one MvPowerSeries.blockPermEmbed_apply"

set_option autoImplicit false

open MvPowerSeries CerednikDrinfeld CerednikDrinfeld.SpecialFormal

namespace KerdegAux

variable {σ R : Type*} [CommRing R]

theorem exists_eq_sum_X_mul [DecidableEq σ] (T : Finset σ) :
    ∀ f : MvPowerSeries σ R, (∀ d : σ →₀ ℕ, (∀ s ∈ T, d s = 0) → coeff d f = 0) →
      ∃ q : σ → MvPowerSeries σ R, f = ∑ s ∈ T, X s * q s := by
  induction T using Finset.induction_on with
  | empty =>
    intro f hf
    refine ⟨fun _ => 0, ?_⟩
    rw [Finset.sum_empty]
    ext d
    rw [map_zero]
    exact hf d (fun s hs => absurd hs (Finset.notMem_empty s))
  | @insert s T hs ih =>
    intro f hf
    let f₀ : MvPowerSeries σ R := fun d => if d s = 0 then coeff d f else 0
    have hf₀ : ∀ d, coeff d f₀ = if d s = 0 then coeff d f else 0 := fun d => rfl
    have hdvd : (X s : MvPowerSeries σ R) ∣ f - f₀ := by
      rw [X_dvd_iff]
      intro d hd
      rw [map_sub, hf₀, if_pos hd, sub_self]
    obtain ⟨q', hq'⟩ := hdvd
    obtain ⟨q, hq⟩ := ih f₀ (by
      intro d hd
      rw [hf₀]
      split_ifs with hds
      · exact hf d (fun t ht => by
          rcases Finset.mem_insert.mp ht with rfl | ht
          · exact hds
          · exact hd t ht)
      · rfl)
    refine ⟨Function.update q s q', ?_⟩
    rw [Finset.sum_insert hs, Function.update_self]
    have hrest : ∑ t ∈ T, X t * Function.update q s q' t = ∑ t ∈ T, X t * q t := by
      refine Finset.sum_congr rfl fun t ht => ?_
      rw [Function.update_of_ne (ne_of_mem_of_not_mem ht hs)]
    rw [hrest, ← hq, ← hq']
    ring

theorem exists_eq_sum_X_mul_of_constantCoeff [Fintype σ] (f : MvPowerSeries σ R)
    (hf : constantCoeff f = 0) : ∃ q : σ → MvPowerSeries σ R, f = ∑ s, X s * q s := by
  classical
  obtain ⟨q, hq⟩ := exists_eq_sum_X_mul (Finset.univ : Finset σ) f (fun d hd => by
    have hd0 : d = 0 := Finsupp.ext fun s => hd s (Finset.mem_univ s)
    rw [hd0, coeff_zero_eq_constantCoeff_apply, hf])
  exact ⟨q, hq⟩

theorem subst_mem_span [Fintype σ] {τ : Type*} {a : σ → MvPowerSeries τ R}
    (ha : ∀ i, constantCoeff (a i) = 0) {f : MvPowerSeries σ R} (hf : constantCoeff f = 0) :
    subst a f ∈ Ideal.span (Set.range a) := by
  have hsa : HasSubst a := hasSubst_of_constantCoeff_zero ha
  obtain ⟨q, hq⟩ := exists_eq_sum_X_mul_of_constantCoeff f hf
  rw [hq, ← coe_substAlgHom hsa, map_sum]
  refine Ideal.sum_mem _ fun s _ => ?_
  rw [map_mul, coe_substAlgHom hsa, subst_X hsa]
  exact Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨s, rfl⟩)

end KerdegAux

theorem solution
    (r : ℕ) [Fact r.Prime] {k : Type} [Field k] [IsAlgClosed k] [CharP k r]
    (j : Zp2 r →+* k) (Φ : FormalODModule r k) (hΦs : Φ.IsSpecial j) (hΦ4 : Φ.HasHeight 4)
    (e e' : ↥(Subring.centralizer (Set.range Φ.actEnd ∪ {Φ.varpiEnd})))
    (M : ℕ) (hee' : e * e' = ((r ^ M : ℕ) : ↥(Subring.centralizer (Set.range Φ.actEnd ∪ {Φ.varpiEnd})))) :
    ∃ m' : ℕ, FormalODModule.HasKernelOfDegree ((e' : MvFormalGroup.End Φ.F).toPowerSeries) (r ^ (2 * m')) := by
  classical
  have hr : r.Prime := Fact.out

  set E' : Series k := (e' : MvFormalGroup.End Φ.F).toPowerSeries with hE'
  have hE'0 : ∀ i, constantCoeff (E' i) = 0 := (e' : MvFormalGroup.End Φ.F).constantCoeff_eq_zero

  set e₁ : ↥(Subring.centralizer (Set.range Φ.actEnd ∪ {Φ.varpiEnd})) := ((r : ℕ) : ↥(Subring.centralizer _)) * e with he₁
  have hee₁ : e₁ * e' = ((r ^ (M + 1) : ℕ) : ↥(Subring.centralizer (Set.range Φ.actEnd ∪ {Φ.varpiEnd}))) := by
    rw [he₁, mul_assoc, hee']
    push_cast
    rw [pow_succ']
  set E₁ : Series k := (e₁ : MvFormalGroup.End Φ.F).toPowerSeries with hE₁
  have hE₁0 : ∀ i, constantCoeff (E₁ i) = 0 := (e₁ : MvFormalGroup.End Φ.F).constantCoeff_eq_zero

  let P : ℕ → Series k := fun m => (((r ^ m : ℕ) : MvFormalGroup.End Φ.F)).toPowerSeries
  have hP0 : ∀ m i, constantCoeff (P m i) = 0 := fun m => (((r ^ m : ℕ) : MvFormalGroup.End Φ.F)).constantCoeff_eq_zero
  have hP1 : P 1 = Φ.act (r : Zp2 r) := by
    show (((r ^ 1 : ℕ) : MvFormalGroup.End Φ.F)).toPowerSeries = _
    rw [pow_one, MvFormalGroup.End.toPowerSeries_natCast, FormalODModule.act_natCast]
  have hPsucc : ∀ m, P (m + 1) = (P m).comp (P 1) := by
    intro m
    show (((r ^ (m + 1) : ℕ) : MvFormalGroup.End Φ.F)).toPowerSeries =
      Series.comp (((r ^ m : ℕ) : MvFormalGroup.End Φ.F)).toPowerSeries (((r ^ 1 : ℕ) : MvFormalGroup.End Φ.F)).toPowerSeries
    rw [pow_succ, pow_one, Nat.cast_mul]
    rfl

  have hPdeg : ∀ m, FormalODModule.HasKernelOfDegree (P (m + 1)) (r ^ (4 * (m + 1))) := by
    intro m
    induction m with
    | zero =>
      rw [hP1]
      simp at hΦ4 ⊢
      exact hΦ4
    | succ m ih =>
      rw [hPsucc]
      have h := FormalODModule.HasKernelOfDegree.comp (hP0 1) (hP0 (m + 1)) (by rw [hP1]; exact hΦ4) ih
      have hdeg' : r ^ 4 * r ^ (4 * (m + 1)) = r ^ (4 * (m + 1 + 1)) := by ring
      rw [hdeg'] at h
      exact h

  obtain ⟨N, hN⟩ := FormalODModule.exists_X_pow_mem_span_of_hasKernelOfDegree (P (M + 1)) (hP0 _) (hPdeg M)

  have hPE : P (M + 1) = E₁.comp E' := by
    show (((r ^ (M + 1) : ℕ) : MvFormalGroup.End Φ.F)).toPowerSeries = _
    have h := congrArg (fun x : ↥(Subring.centralizer (Set.range Φ.actEnd ∪ {Φ.varpiEnd})) => (x : MvFormalGroup.End Φ.F).toPowerSeries) hee₁
    simp only [Subring.coe_mul, Subring.coe_natCast] at h
    rw [← h]
    rfl
  have hle : Ideal.span (Set.range (P (M + 1))) ≤ Ideal.span (Set.range E') := by
    rw [hPE]
    refine Ideal.span_le.mpr ?_
    rintro _ ⟨i, rfl⟩
    exact KerdegAux.subst_mem_span hE'0 (hE₁0 i)
  have hN' : ∃ N : ℕ, ∀ i : Fin 2, (X i : MvPowerSeries (Fin 2) k) ^ N ∈ Ideal.span (Set.range E') :=
    ⟨N, fun i => hle (hN i)⟩

  obtain ⟨d, hd⟩ := FormalODModule.exists_hasKernelOfDegree_of_X_pow_mem_span_of_field E' hE'0 hN'

  have hN1 : ∃ N : ℕ, ∀ i : Fin 2, (X i : MvPowerSeries (Fin 2) k) ^ N ∈ Ideal.span (Set.range E₁) :=
    FormalODModule.exists_X_pow_mem_span_of_X_pow_mem_span_comp hE'0 hE₁0 hd ⟨N, by rw [← hPE]; exact hN⟩
  obtain ⟨d₁, hd₁⟩ := FormalODModule.exists_hasKernelOfDegree_of_X_pow_mem_span_of_field E₁ hE₁0 hN1
  have hcomp := FormalODModule.HasKernelOfDegree.comp hE'0 hE₁0 hd hd₁
  rw [← hPE] at hcomp
  have hdeg : d * d₁ = r ^ (4 * (M + 1)) := by
    have h1 := hcomp.2.2 k (RingHom.id k)
    have h2 := (hPdeg M).2.2 k (RingHom.id k)
    rw [h1] at h2
    exact h2
  have hdvd : d ∣ r ^ (4 * (M + 1)) := ⟨d₁, hdeg.symm⟩
  obtain ⟨h, -, rfl⟩ := (Nat.dvd_prime_pow hr).1 hdvd

  have hOD : FormalODModule.IsODHom Φ Φ E' := by
    refine ⟨IsLawHom.of_hom (e' : MvFormalGroup.End Φ.F), fun a => ?_, ?_⟩
    · have hc := Subring.mem_centralizer_iff.mp e'.2 (Φ.actEnd a) (Set.mem_union_left _ ⟨a, rfl⟩)
      exact (congrArg MvFormalGroup.Hom.toPowerSeries hc).symm
    · have hc := Subring.mem_centralizer_iff.mp e'.2 Φ.varpiEnd (Set.mem_union_right _ (Set.mem_singleton _))
      exact (congrArg MvFormalGroup.Hom.toPowerSeries hc).symm
  let Φb : SpecialFormalODModule r j := ⟨Φ, hΦs, hΦ4⟩
  have heven : Even h :=
    SpecialFormalODModule.even_of_isIsogenyOfHeight_of_isAlgClosed r k j Φb Φb E' h ⟨hOD, hd⟩
  obtain ⟨m', hm'⟩ := heven
  refine ⟨m', ?_⟩
  rw [two_mul, ← hm']
  exact hd

end S_CerednikDrinfeld_FormalODModule_exists_hasKernelOfDegree_pow_two_mul_of_mul_eq_natCast_of_isSpecial_of_hasHeight
end P2MW
export P2MW.S_CerednikDrinfeld_FormalODModule_exists_hasKernelOfDegree_pow_two_mul_of_mul_eq_natCast_of_isSpecial_of_hasHeight (solution)
