-- Prove2me | solution 1 for CohCarrier.levelRaisingComb_mem_parabolicHoms_and_adjoint_and_comp_of_prime
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/5b713306-0eba-5d42-97e0-55e39008e917

import Mathlib
import Definitions.Def_CuspForm_CornerPairingFamily
import Theorems.Thm_CuspForm_Bfam0_block
import Theorems.Thm_CohCarrier_jDeg_iDeg_nine_identities_of_prime
import Theorems.Thm_CohCarrier_heckeT_comm_of_prime
import Theorems.Thm_CohCarrier_iDeg_heckeT_comm_of_coprime
import Theorems.Thm_CohCarrier_iDeg_heckeT_comm_of_dvd
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CohCarrier_levelRaisingComb_mem_parabolicHoms_and_adjoint_and_comp_of_prime
p2m_attr_erase "instance" "ModularCurve.PDPairing.isFreeGroup_inf ModularCurve.PDPairing.instFintypeCusp ModularCurve.PDPairing.iotaDeg0_range_finiteIndex ModularCurve.PDPairing.CentralExt.instInv ModularCurve.PDPairing.CentralExt.instGroup ModularCurve.PDPairing.CentralExt.instMul ModularCurve.PDPairing.CentralExt.instOne ModularCurve.PDPairing.Gamma0Upper_finiteIndex ModularCurve.Period.parabolicHoms_int_moduleFinite ModularCurve.Period.instGroupFG_SL2Z ModularCurve.Period.instIsNoetherian_addHom_int ModularCurve.Period.instGroupFG_Gamma0 HeckeEis.instFiniteIndexHeckeUpper CohCarrier.GammaHLower_finiteIndex"
p2m_attr_erase "simp" "ModularCurve.PDPairing.CentralExt.lift_apply ModularCurve.PDPairing.mem_Gamma0Upper ModularCurve.PDPairing.CentralExt.snd_apply ModularCurve.PDPairing.pairZ_apply ModularCurve.PDPairing.conjUpperMat_apply_11 ModularCurve.PDPairing.sect_snd ModularCurve.PDPairing.conjUpperMat_apply_10 HeckeEis.heckeConjMat_apply_one_one HeckeEis.coe_heckeConjSL HeckeEis.mem_heckeUpperSL HeckeEis.resHom_apply HeckeEis.heckeConjMat_apply_zero_one HeckeEis.coe_transferAux HeckeEis.coe_heckeConj HeckeEis.alphaMat_apply_one_one HeckeEis.heckeConjMat_apply_one_zero HeckeEis.alphaMat_apply_zero_one HeckeEis.pullbackHom_apply HeckeEis.alphaMat_apply_one_zero HeckeEis.alphaMat_apply_zero_zero HeckeEis.heckeConjMat_apply_zero_zero CohCarrier.uMat_apply_10 CohCarrier.rightQuotEquivOfDvd_apply CohCarrier.uMat_apply_11 CohCarrier.uMat_apply_01 CohCarrier.uMat_apply_00 CohCarrier.coe_uElt"

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open Matrix Matrix.SpecialLinearGroup CongruenceSubgroup
open scoped MatrixGroups

namespace MapsSol

section Trace

p2m_open "CohCarrier~jDegL_mem_parabolicHoms"

theorem trace_pow_succ_succ (γ : SL(2, ℤ)) (m : ℕ) :
    ((γ ^ (m + 2) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).trace =
      (γ : Matrix (Fin 2) (Fin 2) ℤ).trace * ((γ ^ (m + 1) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).trace
        - ((γ ^ m : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).trace := by
  have hdet := Matrix.SpecialLinearGroup.det_coe γ
  rw [Matrix.det_fin_two] at hdet
  have h : ((γ ^ (m + 2) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) =
      ((γ ^ m : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) *
        (γ : Matrix (Fin 2) (Fin 2) ℤ) * (γ : Matrix (Fin 2) (Fin 2) ℤ) := by
    rw [Matrix.SpecialLinearGroup.coe_pow, Matrix.SpecialLinearGroup.coe_pow, pow_add, pow_two,
      mul_assoc]
  have h1 : ((γ ^ (m + 1) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) =
      ((γ ^ m : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) * (γ : Matrix (Fin 2) (Fin 2) ℤ) := by
    rw [Matrix.SpecialLinearGroup.coe_pow, Matrix.SpecialLinearGroup.coe_pow, pow_succ]
  rw [h, h1]
  set P : Matrix (Fin 2) (Fin 2) ℤ := ((γ ^ m : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)
  simp only [Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two]
  linear_combination (-(P 0 0 + P 1 1)) * hdet

theorem trace_sq_pow (γ : SL(2, ℤ)) (hγ : ((γ : Matrix (Fin 2) (Fin 2) ℤ).trace) ^ 2 = 4) (m : ℕ) :
    (((γ ^ m : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).trace) ^ 2 = 4 := by
  set t := (γ : Matrix (Fin 2) (Fin 2) ℤ).trace with ht
  have ht2 : t = 2 ∨ t = -2 := by
    have : (t - 2) * (t + 2) = 0 := by nlinarith [hγ]
    rcases mul_eq_zero.mp this with h | h
    · left; linarith
    · right; linarith

  obtain ⟨ε, hε, htε⟩ : ∃ ε : ℤ, ε ^ 2 = 1 ∧ t = 2 * ε := by
    rcases ht2 with h | h
    · exact ⟨1, by norm_num, by rw [h]; norm_num⟩
    · exact ⟨-1, by norm_num, by rw [h]; norm_num⟩
  have key : ∀ n : ℕ, ((γ ^ n : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).trace = 2 * ε ^ n ∧
      ((γ ^ (n + 1) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).trace = 2 * ε ^ (n + 1) := by
    intro n
    induction n with
    | zero =>
      refine ⟨?_, ?_⟩
      · rw [pow_zero, Matrix.SpecialLinearGroup.coe_one, Matrix.trace_one, Fintype.card_fin]
        norm_num
      · rw [zero_add, pow_one, pow_one, ← htε]
    | succ n ih =>
      refine ⟨ih.2, ?_⟩
      rw [trace_pow_succ_succ, ih.1, ih.2, ← ht, htε]
      linear_combination (2 * ε ^ n) * hε
  rw [(key m).1, mul_pow, ← pow_mul, mul_comm m 2, pow_mul, hε, one_pow]
  norm_num

theorem trace_sq_conj_pow (γ r : SL(2, ℤ)) (m : ℕ)
    (hγ : ((γ : Matrix (Fin 2) (Fin 2) ℤ).trace) ^ 2 = 4) :
    (((r⁻¹ * γ ^ m * r : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).trace) ^ 2 = 4 := by
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.trace_mul_comm, ← Matrix.SpecialLinearGroup.coe_mul,
    show r * (r⁻¹ * γ ^ m) = γ ^ m by group]
  exact trace_sq_pow γ hγ m

theorem trace_conjUpperMat (ℓ : ℕ) (X : SL(2, ℤ)) (hX : (ℓ : ℤ) ∣ X 0 1) :
    ((conjUpperMat ℓ X hX : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).trace =
      ((X : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).trace := by
  rw [Matrix.trace_fin_two, Matrix.trace_fin_two]
  simp [conjUpperMat]

theorem trace_conjLowerMat (d : ℕ) (X : SL(2, ℤ)) (hX : (d : ℤ) ∣ X 1 0) :
    ((conjLowerMat d X hX : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).trace =
      ((X : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).trace := by
  rw [Matrix.trace_fin_two, Matrix.trace_fin_two]
  simp [conjLowerMat]

end Trace

section Stable

p2m_open "CohCarrier~jDegL_mem_parabolicHoms"

variable {M : ℕ} {Hs : Subgroup (ZMod M)ˣ} {A : Type*} [AddCommGroup A]

theorem coresAdd_isParabolicHom (K : Subgroup ↥(GammaH M Hs)) [K.FiniteIndex]
    (ψ : Additive ↥K →+ A)
    (hψ : ∀ k : ↥K, ((((k : ↥(GammaH M Hs)) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).trace) ^ 2 = 4 →
      ψ (Additive.ofMul k) = 0) :
    ModularCurve.Period.IsParabolicHom (GammaH M Hs) (coresAdd K ψ) := by
  classical
  intro γ hγ
  haveI : Fintype (Quotient (MulAction.orbitRel (Subgroup.zpowers γ) (↥(GammaH M Hs) ⧸ K))) :=
    Fintype.ofFinite _
  change Multiplicative.toAdd (MonoidHom.transfer (AddMonoidHom.toMultiplicativeRight ψ) γ) = 0
  rw [MonoidHom.transfer_eq_prod_quotient_orbitRel_zpowers_quot, toAdd_prod]
  refine Finset.sum_eq_zero fun O _ => hψ _ ?_
  show ((((O.out.out⁻¹ * γ ^ Function.minimalPeriod (γ • ·) O.out * O.out.out : ↥(GammaH M Hs)) :
    SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).trace) ^ 2 = 4
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_pow]
  exact trace_sq_conj_pow _ _ _ hγ

theorem heckeTL_mem_parabolicHoms (𝒪 : Type) [CommRing 𝒪] (ℓ : ℕ) [NeZero ℓ] (φ : H1 M Hs 𝒪)
    (hφ : φ ∈ ModularCurve.Period.parabolicHoms 𝒪 (GammaH M Hs) 𝒪) :
    heckeTL M Hs 𝒪 ℓ φ ∈ ModularCurve.Period.parabolicHoms 𝒪 (GammaH M Hs) 𝒪 := by
  rw [ModularCurve.Period.mem_parabolicHoms_iff] at hφ ⊢
  refine coresAdd_isParabolicHom (GammaHUpper M Hs ℓ) _ fun k hk => hφ _ ?_
  show ((((conjL M Hs ℓ k : ↥(GammaH M Hs)) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).trace) ^ 2 = 4
  have hx : ((conjL M Hs ℓ k : ↥(GammaH M Hs)) : SL(2, ℤ)) =
      conjUpperMat ℓ ((k : ↥(GammaH M Hs)) : SL(2, ℤ)) (dvd_of_mem_GammaHUpper M Hs ℓ k) := rfl
  rw [hx, trace_conjUpperMat]
  exact hk

theorem heckeT_mem_parabolicHoms (𝒪 : Type) [CommRing 𝒪] (ℓ : ℕ) [NeZero ℓ] (φ : H1 M Hs 𝒪)
    (hφ : φ ∈ ModularCurve.Period.parabolicHoms 𝒪 (GammaH M Hs) 𝒪) :
    heckeT M Hs ℓ 𝒪 φ ∈ ModularCurve.Period.parabolicHoms 𝒪 (GammaH M Hs) 𝒪 :=
  heckeTL_mem_parabolicHoms 𝒪 ℓ φ hφ

variable {M' : ℕ} {Hs' : Subgroup (ZMod M')ˣ} {d : ℕ} [NeZero d]

theorem iDegL_mem_parabolicHoms (𝒪 : Type) [CommRing 𝒪] (h : LevelLE M M' Hs Hs' d) (φ : H1 M Hs 𝒪)
    (hφ : φ ∈ ModularCurve.Period.parabolicHoms 𝒪 (GammaH M Hs) 𝒪) :
    iDegL M M' Hs Hs' d 𝒪 𝒪 h φ ∈ ModularCurve.Period.parabolicHoms 𝒪 (GammaH M' Hs') 𝒪 := by
  rw [ModularCurve.Period.mem_parabolicHoms_iff] at hφ ⊢
  intro γ hγ
  show φ (Additive.ofMul (iotaDeg M M' Hs Hs' d h γ)) = 0
  refine hφ _ ?_
  show (((conjLowerMat d (γ : SL(2, ℤ)) (h.dvd_entry γ) : SL(2, ℤ)) :
    Matrix (Fin 2) (Fin 2) ℤ).trace) ^ 2 = 4
  rw [trace_conjLowerMat]
  exact hγ

theorem jDegL_mem_parabolicHoms (𝒪 : Type) [CommRing 𝒪] [NeZero M'] (h : LevelLE M M' Hs Hs' d)
    (ψ : H1 M' Hs' 𝒪) (hψ : ψ ∈ ModularCurve.Period.parabolicHoms 𝒪 (GammaH M' Hs') 𝒪) :
    jDegL M M' Hs Hs' d 𝒪 𝒪 h ψ ∈ ModularCurve.Period.parabolicHoms 𝒪 (GammaH M Hs) 𝒪 := by
  rw [ModularCurve.Period.mem_parabolicHoms_iff] at hψ ⊢
  refine coresAdd_isParabolicHom (iotaDeg M M' Hs Hs' d h).range _ fun k hk => ?_
  set γ' := ((iotaDeg M M' Hs Hs' d h).ofInjective (iotaDeg_injective M M' Hs Hs' d h)).symm k
    with hγ'
  have hval : pushChar M M' Hs Hs' d 𝒪 h ψ (Additive.ofMul k) = ψ (Additive.ofMul γ') := rfl
  rw [hval]
  refine hψ γ' ?_
  have hk' : (k : ↥(GammaH M Hs)) = iotaDeg M M' Hs Hs' d h γ' :=
    (MonoidHom.apply_ofInjective_symm (iotaDeg_injective M M' Hs Hs' d h) k).symm
  have htr : ((((k : ↥(GammaH M Hs)) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).trace) =
      (((γ' : ↥(GammaH M' Hs')) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).trace := by
    rw [hk']
    exact trace_conjLowerMat d _ (h.dvd_entry γ')
  rw [← htr]
  exact hk

theorem jDeg_mem_parabolicHoms (𝒪 : Type) [CommRing 𝒪] [NeZero M'] (h : LevelLE M M' Hs Hs' d)
    (ψ : H1 M' Hs' 𝒪) (hψ : ψ ∈ ModularCurve.Period.parabolicHoms 𝒪 (GammaH M' Hs') 𝒪) :
    jDeg M M' Hs Hs' d 𝒪 h ψ ∈ ModularCurve.Period.parabolicHoms 𝒪 (GammaH M Hs) 𝒪 :=
  jDegL_mem_parabolicHoms 𝒪 h ψ hψ

theorem diamondL_top_eq_one (𝒪 : Type) [CommRing 𝒪] [NeZero M] (u : (ZMod M)ˣ) :
    diamondL M ⊤ 𝒪 u = 1 := by
  apply LinearMap.ext
  intro φ
  set σ : Gamma0 M := Classical.choose (gamma0Units_surjective M u) with hσ
  have hσH : (σ : SL(2, ℤ)) ∈ GammaH M ⊤ := by rw [GammaH_top]; exact σ.2
  set s : ↥(GammaH M ⊤) := ⟨(σ : SL(2, ℤ)), hσH⟩ with hs
  apply AddMonoidHom.ext
  intro x
  show φ (Additive.ofMul (conjHom M ⊤ σ (Additive.toMul x))) = φ x
  have hconj : conjHom M ⊤ σ (Additive.toMul x) = s * Additive.toMul x * s⁻¹ := Subtype.ext rfl
  rw [hconj, ofMul_mul, ofMul_mul, ofMul_inv, map_add, map_add, map_neg, ofMul_toMul]
  abel

end Stable

section Maps

p2m_open "CohCarrier~jDegL_mem_parabolicHoms"

variable (𝒪 : Type) [CommRing 𝒪] (N q : ℕ) [NeZero N] [NeZero q]
  (h1 : LevelLE N (N * q ^ 2) (⊤ : Subgroup (ZMod N)ˣ) (⊤ : Subgroup (ZMod (N * q ^ 2))ˣ) 1)
  (hq' : LevelLE N (N * q ^ 2) (⊤ : Subgroup (ZMod N)ˣ) (⊤ : Subgroup (ZMod (N * q ^ 2))ˣ) q)
  (hq2 : LevelLE N (N * q ^ 2) (⊤ : Subgroup (ZMod N)ˣ) (⊤ : Subgroup (ZMod (N * q ^ 2))ˣ) (q ^ 2))

noncomputable def wMap : H1 N ⊤ 𝒪 →ₗ[𝒪] H1 (N * q ^ 2) ⊤ 𝒪 :=
  (q : 𝒪) • iDegL N (N * q ^ 2) ⊤ ⊤ 1 𝒪 𝒪 h1
    - (iDegL N (N * q ^ 2) ⊤ ⊤ q 𝒪 𝒪 hq').comp (heckeTL N ⊤ 𝒪 q)
    + iDegL N (N * q ^ 2) ⊤ ⊤ (q ^ 2) 𝒪 𝒪 hq2

noncomputable def wDag : H1 (N * q ^ 2) ⊤ 𝒪 →ₗ[𝒪] H1 N ⊤ 𝒪 :=
  (q : 𝒪) • jDegL N (N * q ^ 2) ⊤ ⊤ (q ^ 2) 𝒪 𝒪 hq2
    - (heckeTL N ⊤ 𝒪 q).comp (jDegL N (N * q ^ 2) ⊤ ⊤ q 𝒪 𝒪 hq')
    + jDegL N (N * q ^ 2) ⊤ ⊤ 1 𝒪 𝒪 h1

theorem wMap_apply (φ : H1 N ⊤ 𝒪) :
    wMap 𝒪 N q h1 hq' hq2 φ =
      (q : 𝒪) • iDegL N (N * q ^ 2) ⊤ ⊤ 1 𝒪 𝒪 h1 φ
        - iDegL N (N * q ^ 2) ⊤ ⊤ q 𝒪 𝒪 hq' (heckeTL N ⊤ 𝒪 q φ)
        + iDegL N (N * q ^ 2) ⊤ ⊤ (q ^ 2) 𝒪 𝒪 hq2 φ := rfl

theorem wDag_apply (ψ : H1 (N * q ^ 2) ⊤ 𝒪) :
    wDag 𝒪 N q h1 hq' hq2 ψ =
      (q : 𝒪) • jDegL N (N * q ^ 2) ⊤ ⊤ (q ^ 2) 𝒪 𝒪 hq2 ψ
        - heckeTL N ⊤ 𝒪 q (jDegL N (N * q ^ 2) ⊤ ⊤ q 𝒪 𝒪 hq' ψ)
        + jDegL N (N * q ^ 2) ⊤ ⊤ 1 𝒪 𝒪 h1 ψ := rfl

theorem wMap_mem_parabolicHoms (φ : H1 N ⊤ 𝒪)
    (hφ : φ ∈ ModularCurve.Period.parabolicHoms 𝒪 (GammaH N ⊤) 𝒪) :
    wMap 𝒪 N q h1 hq' hq2 φ ∈ ModularCurve.Period.parabolicHoms 𝒪 (GammaH (N * q ^ 2) ⊤) 𝒪 := by
  rw [wMap_apply]
  refine Submodule.add_mem _ (Submodule.sub_mem _ (Submodule.smul_mem _ _ ?_) ?_) ?_
  · exact iDegL_mem_parabolicHoms 𝒪 h1 φ hφ
  · exact iDegL_mem_parabolicHoms 𝒪 hq' _ (heckeTL_mem_parabolicHoms 𝒪 q φ hφ)
  · exact iDegL_mem_parabolicHoms 𝒪 hq2 φ hφ

theorem wDag_mem_parabolicHoms (ψ : H1 (N * q ^ 2) ⊤ 𝒪)
    (hψ : ψ ∈ ModularCurve.Period.parabolicHoms 𝒪 (GammaH (N * q ^ 2) ⊤) 𝒪) :
    wDag 𝒪 N q h1 hq' hq2 ψ ∈ ModularCurve.Period.parabolicHoms 𝒪 (GammaH N ⊤) 𝒪 := by
  rw [wDag_apply]
  refine Submodule.add_mem _ (Submodule.sub_mem _ (Submodule.smul_mem _ _ ?_) ?_) ?_
  · exact jDegL_mem_parabolicHoms 𝒪 hq2 ψ hψ
  · exact heckeTL_mem_parabolicHoms 𝒪 q _ (jDegL_mem_parabolicHoms 𝒪 hq' ψ hψ)
  · exact jDegL_mem_parabolicHoms 𝒪 h1 ψ hψ

variable {𝒪 N q}

theorem iDegL_eq_iDeg' {M M' : ℕ} {H : Subgroup (ZMod M)ˣ} {H' : Subgroup (ZMod M')ˣ} {d : ℕ} [NeZero d]
    (h : LevelLE M M' H H' d) (φ : H1 M H 𝒪) :
    iDegL M M' H H' d 𝒪 𝒪 h φ = iDeg' M M' H H' d 𝒪 h φ := rfl

theorem jDegL_eq_jDeg {M M' : ℕ} {H : Subgroup (ZMod M)ˣ} {H' : Subgroup (ZMod M')ˣ} {d : ℕ} [NeZero d]
    [NeZero M'] (h : LevelLE M M' H H' d) (ψ : H1 M' H' 𝒪) :
    jDegL M M' H H' d 𝒪 𝒪 h ψ = jDeg M M' H H' d 𝒪 h ψ := rfl

variable (hq : q.Prime)
include hq

theorem nine (hqN : ¬ q ∣ N) (φ : H1 N ⊤ 𝒪) :
    jDegL N (N * q ^ 2) ⊤ ⊤ 1 𝒪 𝒪 h1 (iDegL N (N * q ^ 2) ⊤ ⊤ 1 𝒪 𝒪 h1 φ) =
        ((q : 𝒪) * ((q : 𝒪) + 1)) • φ ∧
    jDegL N (N * q ^ 2) ⊤ ⊤ q 𝒪 𝒪 hq' (iDegL N (N * q ^ 2) ⊤ ⊤ q 𝒪 𝒪 hq' φ) =
        ((q : 𝒪) * ((q : 𝒪) + 1)) • φ ∧
    jDegL N (N * q ^ 2) ⊤ ⊤ (q ^ 2) 𝒪 𝒪 hq2 (iDegL N (N * q ^ 2) ⊤ ⊤ (q ^ 2) 𝒪 𝒪 hq2 φ) =
        ((q : 𝒪) * ((q : 𝒪) + 1)) • φ ∧
    jDegL N (N * q ^ 2) ⊤ ⊤ 1 𝒪 𝒪 h1 (iDegL N (N * q ^ 2) ⊤ ⊤ q 𝒪 𝒪 hq' φ) =
        (q : 𝒪) • heckeTL N ⊤ 𝒪 q φ ∧
    jDegL N (N * q ^ 2) ⊤ ⊤ q 𝒪 𝒪 hq' (iDegL N (N * q ^ 2) ⊤ ⊤ 1 𝒪 𝒪 h1 φ) =
        (q : 𝒪) • heckeTL N ⊤ 𝒪 q φ ∧
    jDegL N (N * q ^ 2) ⊤ ⊤ q 𝒪 𝒪 hq' (iDegL N (N * q ^ 2) ⊤ ⊤ (q ^ 2) 𝒪 𝒪 hq2 φ) =
        (q : 𝒪) • heckeTL N ⊤ 𝒪 q φ ∧
    jDegL N (N * q ^ 2) ⊤ ⊤ (q ^ 2) 𝒪 𝒪 hq2 (iDegL N (N * q ^ 2) ⊤ ⊤ q 𝒪 𝒪 hq' φ) =
        (q : 𝒪) • heckeTL N ⊤ 𝒪 q φ ∧
    jDegL N (N * q ^ 2) ⊤ ⊤ 1 𝒪 𝒪 h1 (iDegL N (N * q ^ 2) ⊤ ⊤ (q ^ 2) 𝒪 𝒪 hq2 φ) =
        heckeTL N ⊤ 𝒪 q (heckeTL N ⊤ 𝒪 q φ) - ((q : 𝒪) + 1) • φ ∧
    jDegL N (N * q ^ 2) ⊤ ⊤ (q ^ 2) 𝒪 𝒪 hq2 (iDegL N (N * q ^ 2) ⊤ ⊤ 1 𝒪 𝒪 h1 φ) =
        heckeTL N ⊤ 𝒪 q (heckeTL N ⊤ 𝒪 q φ) - ((q : 𝒪) + 1) • φ := by
  obtain ⟨e11, eqq, e22, e1q, eq1, eq2, e2q, e12, e21⟩ :=
    jDeg_iDeg_nine_identities_of_prime N q 𝒪 hq hqN h1 hq' hq2
  have cast1 : ∀ ψ : H1 N ⊤ 𝒪, ((q * (q + 1) : ℤ)) • ψ = ((q : 𝒪) * ((q : 𝒪) + 1)) • ψ := by
    intro ψ
    rw [← Int.cast_smul_eq_zsmul 𝒪]
    push_cast
    rfl
  have cast2 : ∀ ψ : H1 N ⊤ 𝒪, (q : ℤ) • ψ = (q : 𝒪) • ψ := by
    intro ψ
    rw [← Int.cast_smul_eq_zsmul 𝒪]
    push_cast
    rfl
  have cast3 : ∀ ψ : H1 N ⊤ 𝒪, ((q : ℤ) + 1) • ψ = ((q : 𝒪) + 1) • ψ := by
    intro ψ
    rw [← Int.cast_smul_eq_zsmul 𝒪]
    push_cast
    rfl
  simp only [AddMonoidHom.comp_apply, cast1, cast2, cast3] at e11 eqq e22 e1q eq1 eq2 e2q e12 e21
  exact ⟨e11 φ, eqq φ, e22 φ, e1q φ, eq1 φ, eq2 φ, e2q φ, e12 φ, e21 φ⟩

theorem wDag_wMap (hqN : ¬ q ∣ N) (φ : H1 N ⊤ 𝒪) :
    wDag 𝒪 N q h1 hq' hq2 (wMap 𝒪 N q h1 hq' hq2 φ) =
      ((q : 𝒪) - 1) • ((((q : 𝒪) + 1) ^ 2) • φ - heckeT N ⊤ q 𝒪 (heckeT N ⊤ q 𝒪 φ)) := by
  rw [wMap_apply, wDag_apply]
  simp only [map_add, map_sub, map_smul]
  obtain ⟨e11, -, -, -, eq1, -, -, -, e21⟩ := nine h1 hq' hq2 hq hqN φ
  obtain ⟨-, eqq, -, e1q, -, -, e2q, -, -⟩ := nine h1 hq' hq2 hq hqN (heckeTL N ⊤ 𝒪 q φ)
  obtain ⟨-, -, e22, -, -, eq2, -, e12, -⟩ := nine h1 hq' hq2 hq hqN φ
  rw [e11, eq1, e21, eqq, e1q, e2q, e22, eq2, e12]
  simp only [map_smul, ← heckeTL_apply]
  module

theorem wMap_heckeT_comm (ℓ : ℕ) [NeZero ℓ] (hℓ : ℓ.Prime) (hℓq : ℓ ≠ q) (φ : H1 N ⊤ 𝒪) :
    wMap 𝒪 N q h1 hq' hq2 (heckeT N ⊤ ℓ 𝒪 φ) =
      heckeT (N * q ^ 2) ⊤ ℓ 𝒪 (wMap 𝒪 N q h1 hq' hq2 φ) := by
  have hcop1 : Nat.Coprime ℓ 1 := Nat.coprime_one_right ℓ
  have hcopq : Nat.Coprime ℓ q := (Nat.coprime_primes hℓ hq).mpr hℓq
  have hcopq2 : Nat.Coprime ℓ (q ^ 2) := hcopq.pow_right 2

  have hcomm : ∀ (d : ℕ) [NeZero d] (h : LevelLE N (N * q ^ 2) ⊤ ⊤ d), Nat.Coprime ℓ d →
      ∀ ψ : H1 N ⊤ 𝒪, iDegL N (N * q ^ 2) ⊤ ⊤ d 𝒪 𝒪 h (heckeT N ⊤ ℓ 𝒪 ψ) =
        heckeT (N * q ^ 2) ⊤ ℓ 𝒪 (iDegL N (N * q ^ 2) ⊤ ⊤ d 𝒪 𝒪 h ψ) := by
    intro d _ h hd ψ
    rw [iDegL_eq_iDeg', iDegL_eq_iDeg']
    by_cases hℓN : ℓ ∣ N
    · exact iDeg_heckeT_comm_of_dvd h hd hℓN ψ
    · have hℓM' : ¬ ℓ ∣ N * q ^ 2 := by
        intro hdvd
        rcases (Nat.Prime.dvd_mul hℓ).mp hdvd with h' | h'
        · exact hℓN h'
        · exact hℓq ((Nat.prime_dvd_prime_iff_eq hℓ hq).mp (hℓ.dvd_of_dvd_pow h'))
      exact iDeg_heckeT_comm_of_coprime h hd hℓ hℓM' ψ
  rw [wMap_apply, wMap_apply]
  conv_rhs => rw [← heckeTL_apply (N * q ^ 2) ⊤ 𝒪 ℓ, map_add, map_sub, map_smul]
  simp only [heckeTL_apply]
  rw [hcomm 1 h1 hcop1, hcomm (q ^ 2) hq2 hcopq2, ← hcomm q hq' hcopq,
    heckeT_comm_of_prime N ⊤ q ℓ hq hcopq.symm φ]

end Maps

section Pairing

p2m_open "CohCarrier~jDegL_mem_parabolicHoms"

theorem bilin_comb_left {R V W : Type*} [CommRing R] [AddCommGroup V] [Module R V] [AddCommGroup W]
    [Module R W] (B : V →ₗ[R] W →ₗ[R] R) (c : R) (a b d : V) (x : W) :
    B (c • a - b + d) x = c * B a x - B b x + B d x := by
  rw [LinearMap.map_add₂, LinearMap.map_sub₂, LinearMap.map_smul₂, smul_eq_mul]

theorem bilin_comb_right {R V W : Type*} [CommRing R] [AddCommGroup V] [Module R V] [AddCommGroup W]
    [Module R W] (B : V →ₗ[R] W →ₗ[R] R) (y : V) (c : R) (a b d : W) :
    B y (c • a - b + d) = c * B y a - B y b + B y d := by
  rw [map_add, map_sub, map_smul, smul_eq_mul]

variable {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [CharZero 𝒪] [IsLocalRing 𝒪]
  (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (hpu : ¬ IsUnit (p : 𝒪))
  (N q : ℕ) [NeZero N] [NeZero q]
  (h1 : LevelLE N (N * q ^ 2) (⊤ : Subgroup (ZMod N)ˣ) (⊤ : Subgroup (ZMod (N * q ^ 2))ˣ) 1)
  (hq' : LevelLE N (N * q ^ 2) (⊤ : Subgroup (ZMod N)ˣ) (⊤ : Subgroup (ZMod (N * q ^ 2))ˣ) q)
  (hq2 : LevelLE N (N * q ^ 2) (⊤ : Subgroup (ZMod N)ˣ) (⊤ : Subgroup (ZMod (N * q ^ 2))ˣ) (q ^ 2))

include hp hp2 hpu

set_option maxHeartbeats 1600000 in

theorem adjoint
    (x jy : ↥(ModularCurve.Period.parabolicHoms 𝒪 (GammaH N ⊤) 𝒪))
    (y wx : ↥(ModularCurve.Period.parabolicHoms 𝒪 (GammaH (N * q ^ 2) ⊤) 𝒪))
    (hwx : wx.1 = wMap 𝒪 N q h1 hq' hq2 x.1)
    (hjy : jy.1 = wDag 𝒪 N q h1 hq' hq2 y.1) :
    CuspForm.Bfam₀ 𝒪 N jy x = CuspForm.Bfam₀ 𝒪 (N * q ^ 2) y wx := by
  obtain ⟨hlev, hdeg⟩ := CuspForm.Bfam0.block (𝒪 := 𝒪) p hp hp2 hpu
  obtain ⟨-, hTadj, -⟩ := hlev N
  have hN : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  have hdd : (1 : ℕ) * q ^ 2 = N * q ^ 2 / N := by rw [one_mul, Nat.mul_div_cancel_left _ hN]
  have hdd' : q * q = N * q ^ 2 / N := by rw [← pow_two, Nat.mul_div_cancel_left _ hN]
  have hdd'' : q ^ 2 * 1 = N * q ^ 2 / N := by rw [mul_one, Nat.mul_div_cancel_left _ hN]

  obtain ⟨i1x, hi1x⟩ : ∃ v : ↥(ModularCurve.Period.parabolicHoms 𝒪 (GammaH (N * q ^ 2) ⊤) 𝒪),
      v.1 = iDegL N (N * q ^ 2) ⊤ ⊤ 1 𝒪 𝒪 h1 x.1 := ⟨⟨_, iDegL_mem_parabolicHoms 𝒪 h1 _ x.2⟩, rfl⟩
  obtain ⟨Tx, hTx⟩ : ∃ v : ↥(ModularCurve.Period.parabolicHoms 𝒪 (GammaH N ⊤) 𝒪),
      v.1 = heckeTL N ⊤ 𝒪 q x.1 := ⟨⟨_, heckeTL_mem_parabolicHoms 𝒪 q _ x.2⟩, rfl⟩
  obtain ⟨iqTx, hiqTx⟩ : ∃ v : ↥(ModularCurve.Period.parabolicHoms 𝒪 (GammaH (N * q ^ 2) ⊤) 𝒪),
      v.1 = iDegL N (N * q ^ 2) ⊤ ⊤ q 𝒪 𝒪 hq' Tx.1 := ⟨⟨_, iDegL_mem_parabolicHoms 𝒪 hq' _ Tx.2⟩, rfl⟩
  obtain ⟨i2x, hi2x⟩ : ∃ v : ↥(ModularCurve.Period.parabolicHoms 𝒪 (GammaH (N * q ^ 2) ⊤) 𝒪),
      v.1 = iDegL N (N * q ^ 2) ⊤ ⊤ (q ^ 2) 𝒪 𝒪 hq2 x.1 :=
    ⟨⟨_, iDegL_mem_parabolicHoms 𝒪 hq2 _ x.2⟩, rfl⟩
  obtain ⟨j2y, hj2y⟩ : ∃ v : ↥(ModularCurve.Period.parabolicHoms 𝒪 (GammaH N ⊤) 𝒪),
      v.1 = jDegL N (N * q ^ 2) ⊤ ⊤ (q ^ 2) 𝒪 𝒪 hq2 y.1 :=
    ⟨⟨_, jDegL_mem_parabolicHoms 𝒪 hq2 _ y.2⟩, rfl⟩
  obtain ⟨jqy, hjqy⟩ : ∃ v : ↥(ModularCurve.Period.parabolicHoms 𝒪 (GammaH N ⊤) 𝒪),
      v.1 = jDegL N (N * q ^ 2) ⊤ ⊤ q 𝒪 𝒪 hq' y.1 := ⟨⟨_, jDegL_mem_parabolicHoms 𝒪 hq' _ y.2⟩, rfl⟩
  obtain ⟨Tjqy, hTjqy⟩ : ∃ v : ↥(ModularCurve.Period.parabolicHoms 𝒪 (GammaH N ⊤) 𝒪),
      v.1 = heckeTL N ⊤ 𝒪 q jqy.1 := ⟨⟨_, heckeTL_mem_parabolicHoms 𝒪 q _ jqy.2⟩, rfl⟩
  obtain ⟨j1y, hj1y⟩ : ∃ v : ↥(ModularCurve.Period.parabolicHoms 𝒪 (GammaH N ⊤) 𝒪),
      v.1 = jDegL N (N * q ^ 2) ⊤ ⊤ 1 𝒪 𝒪 h1 y.1 := ⟨⟨_, jDegL_mem_parabolicHoms 𝒪 h1 _ y.2⟩, rfl⟩
  have hwx' : wx = (q : 𝒪) • i1x - iqTx + i2x := by
    apply Subtype.ext
    rw [Submodule.coe_add, Submodule.coe_sub, Submodule.coe_smul]
    change wx.1 = (q : 𝒪) • i1x.1 - iqTx.1 + i2x.1
    rw [hwx, wMap_apply, hi1x, hiqTx, hTx, hi2x]
  have hjy' : jy = (q : 𝒪) • j2y - Tjqy + j1y := by
    apply Subtype.ext
    rw [Submodule.coe_add, Submodule.coe_sub, Submodule.coe_smul]
    change jy.1 = (q : 𝒪) • j2y.1 - Tjqy.1 + j1y.1
    rw [hjy, wDag_apply, hj2y, hTjqy, hjqy, hj1y]

  have e1 : CuspForm.Bfam₀ 𝒪 N j2y x = CuspForm.Bfam₀ 𝒪 (N * q ^ 2) y i1x :=
    hdeg N (N * q ^ 2) 1 (q ^ 2) h1 hq2 hdd x y i1x j2y hi1x hj2y
  have e2 : CuspForm.Bfam₀ 𝒪 N Tjqy x = CuspForm.Bfam₀ 𝒪 N jqy Tx :=
    hTadj q jqy x Tjqy Tx hTjqy hTx
  have e3 : CuspForm.Bfam₀ 𝒪 N jqy Tx = CuspForm.Bfam₀ 𝒪 (N * q ^ 2) y iqTx :=
    hdeg N (N * q ^ 2) q q hq' hq' hdd' Tx y iqTx jqy hiqTx hjqy
  have e4 : CuspForm.Bfam₀ 𝒪 N j1y x = CuspForm.Bfam₀ 𝒪 (N * q ^ 2) y i2x :=
    hdeg N (N * q ^ 2) (q ^ 2) 1 hq2 h1 hdd'' x y i2x j1y hi2x hj1y
  have lhs : CuspForm.Bfam₀ 𝒪 N ((q : 𝒪) • j2y - Tjqy + j1y) x =
      (q : 𝒪) * CuspForm.Bfam₀ 𝒪 N j2y x - CuspForm.Bfam₀ 𝒪 N Tjqy x + CuspForm.Bfam₀ 𝒪 N j1y x :=
    bilin_comb_left (CuspForm.Bfam₀ 𝒪 N) (q : 𝒪) j2y Tjqy j1y x
  have rhs : CuspForm.Bfam₀ 𝒪 (N * q ^ 2) y ((q : 𝒪) • i1x - iqTx + i2x) =
      (q : 𝒪) * CuspForm.Bfam₀ 𝒪 (N * q ^ 2) y i1x - CuspForm.Bfam₀ 𝒪 (N * q ^ 2) y iqTx
        + CuspForm.Bfam₀ 𝒪 (N * q ^ 2) y i2x :=
    bilin_comb_right (CuspForm.Bfam₀ 𝒪 (N * q ^ 2)) y (q : 𝒪) i1x iqTx i2x

  calc CuspForm.Bfam₀ 𝒪 N jy x
      = CuspForm.Bfam₀ 𝒪 N ((q : 𝒪) • j2y - Tjqy + j1y) x := by rw [hjy']
    _ = (q : 𝒪) * CuspForm.Bfam₀ 𝒪 N j2y x - CuspForm.Bfam₀ 𝒪 N Tjqy x
          + CuspForm.Bfam₀ 𝒪 N j1y x := lhs
    _ = (q : 𝒪) * CuspForm.Bfam₀ 𝒪 (N * q ^ 2) y i1x - CuspForm.Bfam₀ 𝒪 (N * q ^ 2) y iqTx
          + CuspForm.Bfam₀ 𝒪 (N * q ^ 2) y i2x := by
        linear_combination (q : 𝒪) * e1 - e2 - e3 + e4
    _ = CuspForm.Bfam₀ 𝒪 (N * q ^ 2) y ((q : 𝒪) • i1x - iqTx + i2x) := rhs.symm
    _ = CuspForm.Bfam₀ 𝒪 (N * q ^ 2) y wx := by rw [hwx']

omit hp hp2 hpu in

theorem opFamily_comm (S : Set ℕ) (g g' : Gen N S) :
    opFamily N ⊤ S 𝒪 g * opFamily N ⊤ S 𝒪 g' = opFamily N ⊤ S 𝒪 g' * opFamily N ⊤ S 𝒪 g := by

  have key : ∀ (a b : ℕ) (ha : a.Prime) (hb : b.Prime),
      (haveI : NeZero a := ⟨ha.ne_zero⟩; haveI : NeZero b := ⟨hb.ne_zero⟩;
        heckeTL N ⊤ 𝒪 a * heckeTL N ⊤ 𝒪 b = heckeTL N ⊤ 𝒪 b * heckeTL N ⊤ 𝒪 a) := by
    intro a b ha hb
    haveI : NeZero a := ⟨ha.ne_zero⟩
    haveI : NeZero b := ⟨hb.ne_zero⟩
    by_cases hab : a = b
    · subst hab; rfl
    · apply LinearMap.ext
      intro φ
      exact heckeT_comm_of_prime N ⊤ a b ha ((Nat.coprime_primes ha hb).mpr hab) φ
  rcases g with ⟨ℓ, hℓ, hℓS, hℓN⟩ | ⟨r, hr, hrN⟩ | ⟨d⟩ <;>
    rcases g' with ⟨ℓ', hℓ', hℓS', hℓN'⟩ | ⟨r', hr', hrN'⟩ | ⟨d'⟩ <;>
    simp only [opFamily, diamondL_top_eq_one, one_mul, mul_one]
  · exact key ℓ ℓ' hℓ hℓ'
  · exact key ℓ r' hℓ hr'
  · exact key r ℓ' hr hℓ'
  · exact key r r' hr hr'

theorem par_stable_and_selfAdjoint (S : Set ℕ) (b : Module.End 𝒪 (H1 N ⊤ 𝒪))
    (hb : b ∈ Algebra.adjoin 𝒪 (Set.range (opFamily N ⊤ S 𝒪))) :
    (∀ x : H1 N ⊤ 𝒪, x ∈ ModularCurve.Period.parabolicHoms 𝒪 (GammaH N ⊤) 𝒪 →
        b x ∈ ModularCurve.Period.parabolicHoms 𝒪 (GammaH N ⊤) 𝒪) ∧
    (∀ (x y bx by' : ↥(ModularCurve.Period.parabolicHoms 𝒪 (GammaH N ⊤) 𝒪)),
        (bx : H1 N ⊤ 𝒪) = b (x : H1 N ⊤ 𝒪) → (by' : H1 N ⊤ 𝒪) = b (y : H1 N ⊤ 𝒪) →
        CuspForm.Bfam₀ 𝒪 N bx y = CuspForm.Bfam₀ 𝒪 N x by') := by
  obtain ⟨hlev, -⟩ := CuspForm.Bfam0.block (𝒪 := 𝒪) p hp hp2 hpu
  obtain ⟨-, hTadj, hDadj⟩ := hlev N

  have hgen : ∀ a ∈ Set.range (opFamily N ⊤ S 𝒪), ∀ c ∈ Set.range (opFamily N ⊤ S 𝒪), a * c = c * a := by
    rintro _ ⟨g, rfl⟩ _ ⟨g', rfl⟩
    exact opFamily_comm N S g g'
  have hcommute : ∀ a ∈ Algebra.adjoin 𝒪 (Set.range (opFamily N ⊤ S 𝒪)),
      ∀ c ∈ Algebra.adjoin 𝒪 (Set.range (opFamily N ⊤ S 𝒪)), a * c = c * a := by
    intro a ha c hc
    refine (Algebra.commute_of_mem_adjoin_of_forall_mem_commute hc fun g hg => ?_).eq
    exact ((Algebra.commute_of_mem_adjoin_of_forall_mem_commute ha fun g' hg' =>
      (hgen g hg g' hg')).symm)
  induction hb using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨g, rfl⟩ := hx
    cases g with
    | T ℓ hℓ hℓS hℓL =>
      haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
      show (∀ w : H1 N ⊤ 𝒪, w ∈ _ → heckeTL N ⊤ 𝒪 ℓ w ∈ _) ∧
        (∀ x y bx by' : ↥(ModularCurve.Period.parabolicHoms 𝒪 (GammaH N ⊤) 𝒪),
          (bx : H1 N ⊤ 𝒪) = heckeTL N ⊤ 𝒪 ℓ x → (by' : H1 N ⊤ 𝒪) = heckeTL N ⊤ 𝒪 ℓ y → _)
      exact ⟨fun w hw => heckeTL_mem_parabolicHoms 𝒪 ℓ w hw,
        fun x y bx by' hbx hby => hTadj ℓ x y bx by' hbx hby⟩
    | U r hr hrL =>
      haveI : NeZero r := ⟨hr.ne_zero⟩
      show (∀ w : H1 N ⊤ 𝒪, w ∈ _ → heckeTL N ⊤ 𝒪 r w ∈ _) ∧
        (∀ x y bx by' : ↥(ModularCurve.Period.parabolicHoms 𝒪 (GammaH N ⊤) 𝒪),
          (bx : H1 N ⊤ 𝒪) = heckeTL N ⊤ 𝒪 r x → (by' : H1 N ⊤ 𝒪) = heckeTL N ⊤ 𝒪 r y → _)
      exact ⟨fun w hw => heckeTL_mem_parabolicHoms 𝒪 r w hw,
        fun x y bx by' hbx hby => hTadj r x y bx by' hbx hby⟩
    | dia d =>
      show (∀ w : H1 N ⊤ 𝒪, w ∈ _ → diamondL N ⊤ 𝒪 d w ∈ _) ∧
        (∀ x y bx by' : ↥(ModularCurve.Period.parabolicHoms 𝒪 (GammaH N ⊤) 𝒪),
          (bx : H1 N ⊤ 𝒪) = diamondL N ⊤ 𝒪 d x → (by' : H1 N ⊤ 𝒪) = diamondL N ⊤ 𝒪 d y → _)
      refine ⟨fun w hw => ?_, fun x y bx by' hbx hby => hDadj d x y bx by' hbx hby⟩
      rw [diamondL_top_eq_one]
      exact hw
  | algebraMap r =>
    refine ⟨fun w hw => ?_, fun x y bx by' hbx hby => ?_⟩
    · rw [Module.algebraMap_end_apply]
      exact Submodule.smul_mem _ r hw
    · rw [Module.algebraMap_end_apply] at hbx hby
      have hbx' : bx = r • x := Subtype.ext hbx
      have hby'' : by' = r • y := Subtype.ext hby
      rw [hbx', hby'', LinearMap.map_smul₂, map_smul]
  | add a c ha hc iha ihc =>
    refine ⟨fun w hw => ?_, fun x y bx by' hbx hby => ?_⟩
    · rw [LinearMap.add_apply]
      exact Submodule.add_mem _ (iha.1 w hw) (ihc.1 w hw)
    · let ax : ↥(ModularCurve.Period.parabolicHoms 𝒪 (GammaH N ⊤) 𝒪) := ⟨a x, iha.1 _ x.2⟩
      let cx : ↥(ModularCurve.Period.parabolicHoms 𝒪 (GammaH N ⊤) 𝒪) := ⟨c x, ihc.1 _ x.2⟩
      let ay : ↥(ModularCurve.Period.parabolicHoms 𝒪 (GammaH N ⊤) 𝒪) := ⟨a y, iha.1 _ y.2⟩
      let cy : ↥(ModularCurve.Period.parabolicHoms 𝒪 (GammaH N ⊤) 𝒪) := ⟨c y, ihc.1 _ y.2⟩
      have hbx' : bx = ax + cx := Subtype.ext (by rw [hbx]; rfl)
      have hby'' : by' = ay + cy := Subtype.ext (by rw [hby]; rfl)
      rw [hbx', hby'', map_add, LinearMap.add_apply, map_add, iha.2 x y ax ay rfl rfl,
        ihc.2 x y cx cy rfl rfl]
  | mul a c ha hc iha ihc =>
    refine ⟨fun w hw => ?_, fun x y bx by' hbx hby => ?_⟩
    · rw [Module.End.mul_apply]
      exact iha.1 _ (ihc.1 w hw)
    · have hcomm' : c * a = a * c := hcommute c hc a ha
      let cx : ↥(ModularCurve.Period.parabolicHoms 𝒪 (GammaH N ⊤) 𝒪) := ⟨c x, ihc.1 _ x.2⟩
      let ay : ↥(ModularCurve.Period.parabolicHoms 𝒪 (GammaH N ⊤) 𝒪) := ⟨a y, iha.1 _ y.2⟩
      have e1 : (bx : H1 N ⊤ 𝒪) = a cx := by rw [hbx]; rfl
      have e2 : (by' : H1 N ⊤ 𝒪) = c ay := by
        rw [hby, ← hcomm']; rfl
      rw [iha.2 cx y bx ay e1 rfl, ihc.2 x ay cx by' rfl e2]

end Pairing

end MapsSol

open MapsSol in
theorem solution
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [CharZero 𝒪] [IsLocalRing 𝒪]
    (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (hpu : ¬ IsUnit (p : 𝒪))
    (N q : ℕ) [NeZero N] [NeZero q] (hq : q.Prime) (hqN : ¬ q ∣ N)
    (h1 : CohCarrier.LevelLE N (N * q ^ 2) (⊤ : Subgroup (ZMod N)ˣ)
      (⊤ : Subgroup (ZMod (N * q ^ 2))ˣ) 1)
    (hq' : CohCarrier.LevelLE N (N * q ^ 2) (⊤ : Subgroup (ZMod N)ˣ)
      (⊤ : Subgroup (ZMod (N * q ^ 2))ˣ) q)
    (hq2 : CohCarrier.LevelLE N (N * q ^ 2) (⊤ : Subgroup (ZMod N)ˣ)
      (⊤ : Subgroup (ZMod (N * q ^ 2))ˣ) (q ^ 2)) :

    (∀ φ : CohCarrier.H1 N ⊤ 𝒪, φ ∈ ModularCurve.Period.parabolicHoms 𝒪 (CohCarrier.GammaH N ⊤) 𝒪 →
      ((q : 𝒪) • CohCarrier.iDegL N (N * q ^ 2) ⊤ ⊤ 1 𝒪 𝒪 h1
          - (CohCarrier.iDegL N (N * q ^ 2) ⊤ ⊤ q 𝒪 𝒪 hq').comp (CohCarrier.heckeTL N ⊤ 𝒪 q)
          + CohCarrier.iDegL N (N * q ^ 2) ⊤ ⊤ (q ^ 2) 𝒪 𝒪 hq2) φ ∈
        ModularCurve.Period.parabolicHoms 𝒪 (CohCarrier.GammaH (N * q ^ 2) ⊤) 𝒪) ∧
    (∀ ψ : CohCarrier.H1 (N * q ^ 2) ⊤ 𝒪,
      ψ ∈ ModularCurve.Period.parabolicHoms 𝒪 (CohCarrier.GammaH (N * q ^ 2) ⊤) 𝒪 →
      ((q : 𝒪) • CohCarrier.jDegL N (N * q ^ 2) ⊤ ⊤ (q ^ 2) 𝒪 𝒪 hq2
          - (CohCarrier.heckeTL N ⊤ 𝒪 q).comp (CohCarrier.jDegL N (N * q ^ 2) ⊤ ⊤ q 𝒪 𝒪 hq')
          + CohCarrier.jDegL N (N * q ^ 2) ⊤ ⊤ 1 𝒪 𝒪 h1) ψ ∈
        ModularCurve.Period.parabolicHoms 𝒪 (CohCarrier.GammaH N ⊤) 𝒪) ∧

    (∀ (x jy : ↥(ModularCurve.Period.parabolicHoms 𝒪 (CohCarrier.GammaH N ⊤) 𝒪))
        (y wx : ↥(ModularCurve.Period.parabolicHoms 𝒪 (CohCarrier.GammaH (N * q ^ 2) ⊤) 𝒪)),
      (wx : CohCarrier.H1 (N * q ^ 2) ⊤ 𝒪) =
        ((q : 𝒪) • CohCarrier.iDegL N (N * q ^ 2) ⊤ ⊤ 1 𝒪 𝒪 h1
          - (CohCarrier.iDegL N (N * q ^ 2) ⊤ ⊤ q 𝒪 𝒪 hq').comp (CohCarrier.heckeTL N ⊤ 𝒪 q)
          + CohCarrier.iDegL N (N * q ^ 2) ⊤ ⊤ (q ^ 2) 𝒪 𝒪 hq2) (x : CohCarrier.H1 N ⊤ 𝒪) →
      (jy : CohCarrier.H1 N ⊤ 𝒪) =
        ((q : 𝒪) • CohCarrier.jDegL N (N * q ^ 2) ⊤ ⊤ (q ^ 2) 𝒪 𝒪 hq2
          - (CohCarrier.heckeTL N ⊤ 𝒪 q).comp (CohCarrier.jDegL N (N * q ^ 2) ⊤ ⊤ q 𝒪 𝒪 hq')
          + CohCarrier.jDegL N (N * q ^ 2) ⊤ ⊤ 1 𝒪 𝒪 h1) (y : CohCarrier.H1 (N * q ^ 2) ⊤ 𝒪) →
      CuspForm.Bfam₀ 𝒪 N jy x = CuspForm.Bfam₀ 𝒪 (N * q ^ 2) y wx) ∧

    (∀ φ : CohCarrier.H1 N ⊤ 𝒪,
      ((q : 𝒪) • CohCarrier.jDegL N (N * q ^ 2) ⊤ ⊤ (q ^ 2) 𝒪 𝒪 hq2
          - (CohCarrier.heckeTL N ⊤ 𝒪 q).comp (CohCarrier.jDegL N (N * q ^ 2) ⊤ ⊤ q 𝒪 𝒪 hq')
          + CohCarrier.jDegL N (N * q ^ 2) ⊤ ⊤ 1 𝒪 𝒪 h1)
        (((q : 𝒪) • CohCarrier.iDegL N (N * q ^ 2) ⊤ ⊤ 1 𝒪 𝒪 h1
          - (CohCarrier.iDegL N (N * q ^ 2) ⊤ ⊤ q 𝒪 𝒪 hq').comp (CohCarrier.heckeTL N ⊤ 𝒪 q)
          + CohCarrier.iDegL N (N * q ^ 2) ⊤ ⊤ (q ^ 2) 𝒪 𝒪 hq2) φ) =
        ((q : 𝒪) - 1) • ((((q : 𝒪) + 1) ^ 2) • φ
          - CohCarrier.heckeT N ⊤ q 𝒪 (CohCarrier.heckeT N ⊤ q 𝒪 φ))) ∧

    (∀ (ℓ : ℕ) [NeZero ℓ], ℓ.Prime → ℓ ≠ q → ∀ φ : CohCarrier.H1 N ⊤ 𝒪,
      ((q : 𝒪) • CohCarrier.iDegL N (N * q ^ 2) ⊤ ⊤ 1 𝒪 𝒪 h1
          - (CohCarrier.iDegL N (N * q ^ 2) ⊤ ⊤ q 𝒪 𝒪 hq').comp (CohCarrier.heckeTL N ⊤ 𝒪 q)
          + CohCarrier.iDegL N (N * q ^ 2) ⊤ ⊤ (q ^ 2) 𝒪 𝒪 hq2) (CohCarrier.heckeT N ⊤ ℓ 𝒪 φ) =
        CohCarrier.heckeT (N * q ^ 2) ⊤ ℓ 𝒪
          (((q : 𝒪) • CohCarrier.iDegL N (N * q ^ 2) ⊤ ⊤ 1 𝒪 𝒪 h1
            - (CohCarrier.iDegL N (N * q ^ 2) ⊤ ⊤ q 𝒪 𝒪 hq').comp (CohCarrier.heckeTL N ⊤ 𝒪 q)
            + CohCarrier.iDegL N (N * q ^ 2) ⊤ ⊤ (q ^ 2) 𝒪 𝒪 hq2) φ)) ∧

    (∀ (S : Set ℕ) (b : Module.End 𝒪 (CohCarrier.H1 N ⊤ 𝒪)),
      b ∈ Algebra.adjoin 𝒪 (Set.range (CohCarrier.opFamily N ⊤ S 𝒪)) →
      (∀ x : CohCarrier.H1 N ⊤ 𝒪, x ∈ ModularCurve.Period.parabolicHoms 𝒪 (CohCarrier.GammaH N ⊤) 𝒪 →
        b x ∈ ModularCurve.Period.parabolicHoms 𝒪 (CohCarrier.GammaH N ⊤) 𝒪) ∧
      (∀ (x y bx by' : ↥(ModularCurve.Period.parabolicHoms 𝒪 (CohCarrier.GammaH N ⊤) 𝒪)),
        (bx : CohCarrier.H1 N ⊤ 𝒪) = b (x : CohCarrier.H1 N ⊤ 𝒪) →
        (by' : CohCarrier.H1 N ⊤ 𝒪) = b (y : CohCarrier.H1 N ⊤ 𝒪) →
        CuspForm.Bfam₀ 𝒪 N bx y = CuspForm.Bfam₀ 𝒪 N x by')) :=
  ⟨fun φ hφ => wMap_mem_parabolicHoms 𝒪 N q h1 hq' hq2 φ hφ,
    fun ψ hψ => wDag_mem_parabolicHoms 𝒪 N q h1 hq' hq2 ψ hψ,
    fun x jy y wx hwx hjy => adjoint p hp hp2 hpu N q h1 hq' hq2 x jy y wx hwx hjy,
    fun φ => wDag_wMap h1 hq' hq2 hq hqN φ,
    fun ℓ _ hℓ hℓq φ => wMap_heckeT_comm h1 hq' hq2 hq ℓ hℓ hℓq φ,
    fun S b hb => par_stable_and_selfAdjoint p hp hp2 hpu N S b hb⟩

end S_CohCarrier_levelRaisingComb_mem_parabolicHoms_and_adjoint_and_comp_of_prime
end P2MW
export P2MW.S_CohCarrier_levelRaisingComb_mem_parabolicHoms_and_adjoint_and_comp_of_prime (solution)
