-- Prove2me | solution 1 for CohCarrier.jDeg_iDeg_corner_of_prime_sq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/11d6bd00-0a90-58bd-bb72-e386a5c226b0

import Definitions.Def_CohCarrier_Level
import Definitions.Def_CohCarrier_Lower
import Theorems.Thm_CohCarrier_jDeg_iDeg_cross_eq_index_smul_heckeT
import Theorems.Thm_CohCarrier_heckeT_iDeg_interchange
import Theorems.Thm_CohCarrier_iotaDeg_comp
import Theorems.Thm_CohCarrier_iDeg_comp
import Theorems.Thm_CohCarrier_jDeg_comp_iDegP_self
import Theorems.Thm_CohCarrier_index_GammaHUpper_of_prime
import Theorems.Thm_CohCarrier_transfer_transitive
import Theorems.Thm_CohCarrier_heckeSym_top_of_coprime
import Theorems.Thm_CohCarrier_jDeg_iDeg_cross_eq_index_smul_heckeTlower_of_coprime
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CohCarrier_jDeg_iDeg_corner_of_prime_sq

set_option autoImplicit false

namespace IharaSolCorner

open CohCarrier
open scoped MatrixGroups

attribute [local instance] Subgroup.fintypeQuotientOfFiniteIndex

section TransferNat

variable {G G' : Type*} [Group G] [Group G']

private noncomputable def quotCongr (e : G ≃* G') (K : Subgroup G) (K' : Subgroup G')
    (hK : ∀ g : G, e g ∈ K' ↔ g ∈ K) : G ⧸ K ≃ G' ⧸ K' :=
  Quotient.congr e.toEquiv fun a b => by
    rw [QuotientGroup.leftRel_apply, QuotientGroup.leftRel_apply]
    show a⁻¹ * b ∈ K ↔ (e a)⁻¹ * e b ∈ K'
    rw [← map_inv, ← map_mul, hK]

private theorem quotCongr_mk (e : G ≃* G') (K : Subgroup G) (K' : Subgroup G')
    (hK : ∀ g : G, e g ∈ K' ↔ g ∈ K) (a : G) :
    quotCongr e K K' hK (a : G ⧸ K) = ((e a : G') : G' ⧸ K') := rfl

private theorem quotCongr_smul (e : G ≃* G') (K : Subgroup G) (K' : Subgroup G')
    (hK : ∀ g : G, e g ∈ K' ↔ g ∈ K) (g : G) (x : G ⧸ K) :
    quotCongr e K K' hK (g • x) = e g • quotCongr e K K' hK x := by
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective x
  show ((e (g * a) : G') : G' ⧸ K') = ((e g * e a : G') : G' ⧸ K')
  rw [map_mul]

private noncomputable def outT (K : Subgroup G) : K.LeftTransversal :=
  ⟨Set.range (Quotient.out : G ⧸ K → G), Subgroup.isComplement_range_left QuotientGroup.out_eq'⟩

private theorem outT_rep (K : Subgroup G) (x : G ⧸ K) :
    ((outT K).2.leftQuotientEquiv x : G) = x.out :=
  Subgroup.IsComplement.leftQuotientEquiv_apply QuotientGroup.out_eq' x

private theorem mapT_section (e : G ≃* G') (K : Subgroup G) (K' : Subgroup G')
    (hK : ∀ g : G, e g ∈ K' ↔ g ∈ K) (y : G' ⧸ K') :
    ((e ((quotCongr e K K' hK).symm y).out : G') : G' ⧸ K') = y := by
  rw [← quotCongr_mk e K K' hK, QuotientGroup.out_eq', Equiv.apply_symm_apply]

private noncomputable def mapT (e : G ≃* G') (K : Subgroup G) (K' : Subgroup G')
    (hK : ∀ g : G, e g ∈ K' ↔ g ∈ K) : K'.LeftTransversal :=
  ⟨Set.range fun y : G' ⧸ K' => e ((quotCongr e K K' hK).symm y).out,
    Subgroup.isComplement_range_left (mapT_section e K K' hK)⟩

private theorem mapT_rep (e : G ≃* G') (K : Subgroup G) (K' : Subgroup G')
    (hK : ∀ g : G, e g ∈ K' ↔ g ∈ K) (y : G' ⧸ K') :
    ((mapT e K K' hK).2.leftQuotientEquiv y : G') = e ((quotCongr e K K' hK).symm y).out :=
  Subgroup.IsComplement.leftQuotientEquiv_apply (mapT_section e K K' hK) y

private theorem quotCongr_symm_inv_smul (e : G ≃* G') (K : Subgroup G) (K' : Subgroup G')
    (hK : ∀ g : G, e g ∈ K' ↔ g ∈ K) (g : G) (y : G' ⧸ K') :
    (quotCongr e K K' hK).symm ((e g)⁻¹ • y) = g⁻¹ • (quotCongr e K K' hK).symm y := by
  rw [Equiv.symm_apply_eq, quotCongr_smul, Equiv.apply_symm_apply, map_inv]

private theorem transfer_comp_mulEquiv {C : Type*} [CommGroup C] (e : G ≃* G')
    (K : Subgroup G) (K' : Subgroup G') [K.FiniteIndex] [K'.FiniteIndex]
    (hK : ∀ g : G, e g ∈ K' ↔ g ∈ K) (ϕ : ↥K →* C) (ϕ' : ↥K' →* C)
    (hϕ : ∀ k : ↥K, ϕ' ⟨e k, (hK k).mpr k.2⟩ = ϕ k) (g : G) :
    MonoidHom.transfer ϕ' (e g) = MonoidHom.transfer ϕ g := by
  rw [MonoidHom.transfer_def ϕ' (mapT e K K' hK), MonoidHom.transfer_def ϕ (outT K)]
  unfold Subgroup.leftTransversals.diff
  refine Fintype.prod_equiv (quotCongr e K K' hK).symm _ _ fun y => ?_
  rw [← hϕ]
  congr 1
  apply Subtype.ext
  show ((mapT e K K' hK).2.leftQuotientEquiv y : G')⁻¹
        * ((e g • mapT e K K' hK).2.leftQuotientEquiv y : G')
      = e (((outT K).2.leftQuotientEquiv ((quotCongr e K K' hK).symm y) : G)⁻¹
        * ((g • outT K).2.leftQuotientEquiv ((quotCongr e K K' hK).symm y) : G))
  rw [Subgroup.smul_apply_eq_smul_apply_inv_smul, Subgroup.smul_apply_eq_smul_apply_inv_smul,
    mapT_rep, mapT_rep, outT_rep, outT_rep, smul_eq_mul, smul_eq_mul, map_mul, map_mul, map_inv,
    quotCongr_symm_inv_smul]

private theorem coresAdd_comp_mulEquiv {B : Type*} [AddCommGroup B] (e : G ≃* G')
    (K : Subgroup G) (K' : Subgroup G') [K.FiniteIndex] [K'.FiniteIndex]
    (hK : ∀ g : G, e g ∈ K' ↔ g ∈ K) (χ : Additive ↥K →+ B) (χ' : Additive ↥K' →+ B)
    (hχ : ∀ k : ↥K, χ' (Additive.ofMul ⟨e k, (hK k).mpr k.2⟩) = χ (Additive.ofMul k)) (g : G) :
    coresAdd K' χ' (Additive.ofMul (e g)) = coresAdd K χ (Additive.ofMul g) := by
  have hϕ : ∀ k : ↥K,
      AddMonoidHom.toMultiplicativeRight χ' ⟨e k, (hK k).mpr k.2⟩
        = AddMonoidHom.toMultiplicativeRight χ k :=
    fun k => congrArg Multiplicative.ofAdd (hχ k)
  exact congrArg Multiplicative.toAdd
    (transfer_comp_mulEquiv e K K' hK (AddMonoidHom.toMultiplicativeRight χ)
      (AddMonoidHom.toMultiplicativeRight χ') hϕ g)

private theorem coresAdd_trans {B : Type*} [AddCommGroup B] (K L : Subgroup G) (hKL : K ≤ L)
    [K.FiniteIndex] [L.FiniteIndex] (χ : Additive ↥K →+ B) (g : G) :
    coresAdd K χ (Additive.ofMul g)
      = coresAdd L (coresAdd (K.subgroupOf L)
          (χ.comp (MonoidHom.toAdditive (Subgroup.subgroupOfEquivOfLe hKL).toMonoidHom)))
          (Additive.ofMul g) := by
  have h1 : AddMonoidHom.toMultiplicativeRight
        (χ.comp (MonoidHom.toAdditive (Subgroup.subgroupOfEquivOfLe hKL).toMonoidHom))
      = (AddMonoidHom.toMultiplicativeRight χ).comp (Subgroup.subgroupOfEquivOfLe hKL).toMonoidHom :=
    MonoidHom.ext fun _ => rfl
  have h2 : AddMonoidHom.toMultiplicativeRight
        (coresAdd (K.subgroupOf L)
          (χ.comp (MonoidHom.toAdditive (Subgroup.subgroupOfEquivOfLe hKL).toMonoidHom)))
      = MonoidHom.transfer (AddMonoidHom.toMultiplicativeRight
          (χ.comp (MonoidHom.toAdditive (Subgroup.subgroupOfEquivOfLe hKL).toMonoidHom))) :=
    MonoidHom.ext fun _ => rfl
  show Multiplicative.toAdd (MonoidHom.transfer (AddMonoidHom.toMultiplicativeRight χ) g)
    = Multiplicative.toAdd (MonoidHom.transfer (AddMonoidHom.toMultiplicativeRight
        (coresAdd (K.subgroupOf L)
          (χ.comp (MonoidHom.toAdditive (Subgroup.subgroupOfEquivOfLe hKL).toMonoidHom)))) g)
  rw [h2, h1, CohCarrier.transfer_transitive K L hKL]

end TransferNat

private theorem rangeIotaQ_eq_upper {N q : ℕ} [NeZero q] [NeZero (N * q)]
    (hq : LevelLE N (N * q) (⊤ : Subgroup (ZMod N)ˣ) (⊤ : Subgroup (ZMod (N * q))ˣ) q) :
    (iotaDeg N (N * q) ⊤ ⊤ q hq).range = GammaHUpper N ⊤ q := by
  have hq0 : (q : ℤ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne q)
  apply le_antisymm
  · rintro x ⟨γ', rfl⟩
    rw [Subgroup.mem_subgroupOf, mem_Gamma0Upper]
    have h01 : ((iotaDeg N (N * q) ⊤ ⊤ q hq γ' : ↥(GammaH N ⊤)) : SL(2, ℤ)) 0 1
        = (γ' : SL(2, ℤ)) 0 1 * q := by
      show (conjLowerMat q (γ' : SL(2, ℤ)) (hq.dvd_entry γ') : SL(2, ℤ)) 0 1
        = (γ' : SL(2, ℤ)) 0 1 * q
      simp [conjLowerMat]
    rw [h01]
    push_cast
    simp
  · intro g hg
    rw [Subgroup.mem_subgroupOf, mem_Gamma0Upper] at hg
    have hb : (q : ℤ) ∣ ((g : ↥(GammaH N ⊤)) : SL(2, ℤ)) 0 1 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (by exact_mod_cast hg)
    have hc : (N : ℤ) ∣ ((g : ↥(GammaH N ⊤)) : SL(2, ℤ)) 1 0 := by
      have h0 : ((g : ↥(GammaH N ⊤)) : SL(2, ℤ)) ∈ CongruenceSubgroup.Gamma0 N := GammaH_le_Gamma0 ⊤ g.2
      rw [CongruenceSubgroup.Gamma0_mem] at h0
      exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h0
    refine ⟨⟨⟨!![((g : ↥(GammaH N ⊤)) : SL(2, ℤ)) 0 0, ((g : ↥(GammaH N ⊤)) : SL(2, ℤ)) 0 1 / q;
              ((g : ↥(GammaH N ⊤)) : SL(2, ℤ)) 1 0 * q, ((g : ↥(GammaH N ⊤)) : SL(2, ℤ)) 1 1],
        ?_⟩, ?_⟩, ?_⟩
    · rw [Matrix.det_fin_two_of]
      have hdet := Matrix.SpecialLinearGroup.det_coe ((g : ↥(GammaH N ⊤)) : SL(2, ℤ))
      rw [Matrix.det_fin_two] at hdet
      have hbc : ((g : ↥(GammaH N ⊤)) : SL(2, ℤ)) 0 1 / q
            * (((g : ↥(GammaH N ⊤)) : SL(2, ℤ)) 1 0 * q)
          = ((g : ↥(GammaH N ⊤)) : SL(2, ℤ)) 0 1 * ((g : ↥(GammaH N ⊤)) : SL(2, ℤ)) 1 0 := by
        rw [mul_comm (((g : ↥(GammaH N ⊤)) : SL(2, ℤ)) 1 0) (q : ℤ), ← mul_assoc,
          Int.ediv_mul_cancel hb]
      rw [hbc]
      exact hdet
    · rw [GammaH_top]
      refine CongruenceSubgroup.Gamma0_mem.mpr ?_
      show ((((g : ↥(GammaH N ⊤)) : SL(2, ℤ)) 1 0 * q : ℤ) : ZMod (N * q)) = 0
      rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
      push_cast
      exact mul_dvd_mul hc dvd_rfl
    · have hdiv01 : ((g : ↥(GammaH N ⊤)) : SL(2, ℤ)) 0 1 / q * q
          = ((g : ↥(GammaH N ⊤)) : SL(2, ℤ)) 0 1 := Int.ediv_mul_cancel hb
      have hdiv10 : ((g : ↥(GammaH N ⊤)) : SL(2, ℤ)) 1 0 * q / q
          = ((g : ↥(GammaH N ⊤)) : SL(2, ℤ)) 1 0 := Int.mul_ediv_cancel _ hq0
      apply Subtype.ext
      refine Matrix.SpecialLinearGroup.ext _ _ fun i j => ?_
      fin_cases i <;> fin_cases j <;>
        simp [iotaDeg, conjLowerMat, Matrix.of_apply, Fin.isValue, hdiv01, hdiv10]

private theorem subgroupOf_rangeIotaQ_index_one {N q : ℕ} [NeZero q] [NeZero (N * q)]
    (hq : LevelLE N (N * q) (⊤ : Subgroup (ZMod N)ˣ) (⊤ : Subgroup (ZMod (N * q))ˣ) q) :
    ((iotaDeg N (N * q) ⊤ ⊤ q hq).range.subgroupOf (GammaHUpper N ⊤ q)).index = 1 := by
  rw [rangeIotaQ_eq_upper, Subgroup.subgroupOf_self, Subgroup.index_top]

private theorem iDeg_comp_eq {M₁ M₂ M₃ d₁ d₂ d₃ : ℕ}
    [NeZero M₂] [NeZero M₃] [NeZero d₁] [NeZero d₂] [NeZero d₃]
    (hd : d₃ = d₁ * d₂)
    (h₁₂ : LevelLE M₁ M₂ (⊤ : Subgroup (ZMod M₁)ˣ) (⊤ : Subgroup (ZMod M₂)ˣ) d₁)
    (h₂₃ : LevelLE M₂ M₃ (⊤ : Subgroup (ZMod M₂)ˣ) (⊤ : Subgroup (ZMod M₃)ˣ) d₂)
    (h₁₃ : LevelLE M₁ M₃ (⊤ : Subgroup (ZMod M₁)ˣ) (⊤ : Subgroup (ZMod M₃)ˣ) d₃)
    (A : Type) [AddCommGroup A] (φ : H1 M₁ ⊤ A) :
    iDeg' M₁ M₃ ⊤ ⊤ d₃ A h₁₃ φ
      = iDeg' M₂ M₃ ⊤ ⊤ d₂ A h₂₃ (iDeg' M₁ M₂ ⊤ ⊤ d₁ A h₁₂ φ) := by
  subst hd
  exact CohCarrier.iDeg_comp h₁₂ h₂₃ h₁₃ φ

private theorem jDeg_comp_eq {M₁ M₂ M₃ d₁ d₂ d₃ : ℕ}
    [NeZero M₂] [NeZero M₃] [NeZero d₁] [NeZero d₂] [NeZero d₃]
    (hd : d₃ = d₁ * d₂)
    (h₁₂ : LevelLE M₁ M₂ (⊤ : Subgroup (ZMod M₁)ˣ) (⊤ : Subgroup (ZMod M₂)ˣ) d₁)
    (h₂₃ : LevelLE M₂ M₃ (⊤ : Subgroup (ZMod M₂)ˣ) (⊤ : Subgroup (ZMod M₃)ˣ) d₂)
    (h₁₃ : LevelLE M₁ M₃ (⊤ : Subgroup (ZMod M₁)ˣ) (⊤ : Subgroup (ZMod M₃)ˣ) d₃)
    (A : Type) [AddCommGroup A] (ψ : H1 M₃ ⊤ A) :
    jDeg M₁ M₃ ⊤ ⊤ d₃ A h₁₃ ψ
      = jDeg M₁ M₂ ⊤ ⊤ d₁ A h₁₂ (jDeg M₂ M₃ ⊤ ⊤ d₂ A h₂₃ ψ) := by
  subst hd
  have hcomp : ∀ γ : ↥(GammaH M₃ ⊤),
      iotaDeg M₁ M₃ ⊤ ⊤ (d₁ * d₂) h₁₃ γ
        = iotaDeg M₁ M₂ ⊤ ⊤ d₁ h₁₂ (iotaDeg M₂ M₃ ⊤ ⊤ d₂ h₂₃ γ) :=
    fun γ => CohCarrier.iotaDeg_comp h₁₂ h₂₃ h₁₃ γ
  have hle : (iotaDeg M₁ M₃ ⊤ ⊤ (d₁ * d₂) h₁₃).range ≤ (iotaDeg M₁ M₂ ⊤ ⊤ d₁ h₁₂).range := by
    rintro _ ⟨γ, rfl⟩
    exact ⟨iotaDeg M₂ M₃ ⊤ ⊤ d₂ h₂₃ γ, (hcomp γ).symm⟩
  have hK : ∀ y : ↥(GammaH M₂ ⊤),
      (iotaDeg M₁ M₂ ⊤ ⊤ d₁ h₁₂).ofInjective (iotaDeg_injective M₁ M₂ ⊤ ⊤ d₁ h₁₂) y
          ∈ (iotaDeg M₁ M₃ ⊤ ⊤ (d₁ * d₂) h₁₃).range.subgroupOf (iotaDeg M₁ M₂ ⊤ ⊤ d₁ h₁₂).range
        ↔ y ∈ (iotaDeg M₂ M₃ ⊤ ⊤ d₂ h₂₃).range := by
    intro y
    rw [Subgroup.mem_subgroupOf]
    show iotaDeg M₁ M₂ ⊤ ⊤ d₁ h₁₂ y ∈ (iotaDeg M₁ M₃ ⊤ ⊤ (d₁ * d₂) h₁₃).range ↔ _
    constructor
    · rintro ⟨γ, hγ⟩
      refine ⟨γ, iotaDeg_injective M₁ M₂ ⊤ ⊤ d₁ h₁₂ ?_⟩
      rw [← hcomp γ, hγ]
    · rintro ⟨γ, rfl⟩
      exact ⟨γ, hcomp γ⟩
  refine AddMonoidHom.ext fun z => ?_
  obtain ⟨γ, rfl⟩ : ∃ γ : ↥(GammaH M₁ ⊤), Additive.ofMul γ = z := ⟨z.toMul, rfl⟩
  show coresAdd _ (pushChar M₁ M₃ ⊤ ⊤ (d₁ * d₂) A h₁₃ ψ) (Additive.ofMul γ)
    = coresAdd _ (pushChar M₁ M₂ ⊤ ⊤ d₁ A h₁₂ (jDeg M₂ M₃ ⊤ ⊤ d₂ A h₂₃ ψ)) (Additive.ofMul γ)
  refine (coresAdd_trans _ _ hle (pushChar M₁ M₃ ⊤ ⊤ (d₁ * d₂) A h₁₃ ψ) γ).trans ?_
  refine congrArg
    (fun χ : Additive ↥(iotaDeg M₁ M₂ ⊤ ⊤ d₁ h₁₂).range →+ A => coresAdd _ χ (Additive.ofMul γ)) ?_
  refine AddMonoidHom.ext fun w => ?_
  obtain ⟨r, rfl⟩ : ∃ r : ↥(iotaDeg M₁ M₂ ⊤ ⊤ d₁ h₁₂).range, Additive.ofMul r = w := ⟨w.toMul, rfl⟩
  obtain ⟨x, rfl⟩ :=
    ((iotaDeg M₁ M₂ ⊤ ⊤ d₁ h₁₂).ofInjective (iotaDeg_injective M₁ M₂ ⊤ ⊤ d₁ h₁₂)).surjective r
  refine (coresAdd_comp_mulEquiv _ _ _ hK (pushChar M₂ M₃ ⊤ ⊤ d₂ A h₂₃ ψ)
    ((pushChar M₁ M₃ ⊤ ⊤ (d₁ * d₂) A h₁₃ ψ).comp
      (MonoidHom.toAdditive (Subgroup.subgroupOfEquivOfLe hle).toMonoidHom)) ?_ x).trans ?_
  · intro k
    obtain ⟨γ', rfl⟩ :=
      ((iotaDeg M₂ M₃ ⊤ ⊤ d₂ h₂₃).ofInjective (iotaDeg_injective M₂ M₃ ⊤ ⊤ d₂ h₂₃)).surjective k
    show ψ (Additive.ofMul
        (((iotaDeg M₁ M₃ ⊤ ⊤ (d₁ * d₂) h₁₃).ofInjective
          (iotaDeg_injective M₁ M₃ ⊤ ⊤ (d₁ * d₂) h₁₃)).symm _))
      = ψ (Additive.ofMul
        (((iotaDeg M₂ M₃ ⊤ ⊤ d₂ h₂₃).ofInjective (iotaDeg_injective M₂ M₃ ⊤ ⊤ d₂ h₂₃)).symm
          (((iotaDeg M₂ M₃ ⊤ ⊤ d₂ h₂₃).ofInjective (iotaDeg_injective M₂ M₃ ⊤ ⊤ d₂ h₂₃)) γ')))
    rw [MulEquiv.symm_apply_apply]
    refine congrArg ψ (congrArg Additive.ofMul ?_)
    rw [MulEquiv.symm_apply_eq]
    apply Subtype.ext
    show iotaDeg M₁ M₂ ⊤ ⊤ d₁ h₁₂ (iotaDeg M₂ M₃ ⊤ ⊤ d₂ h₂₃ γ')
      = iotaDeg M₁ M₃ ⊤ ⊤ (d₁ * d₂) h₁₃ γ'
    exact (hcomp γ').symm
  · show _ = jDeg M₂ M₃ ⊤ ⊤ d₂ A h₂₃ ψ (Additive.ofMul
        (((iotaDeg M₁ M₂ ⊤ ⊤ d₁ h₁₂).ofInjective (iotaDeg_injective M₁ M₂ ⊤ ⊤ d₁ h₁₂)).symm
          (((iotaDeg M₁ M₂ ⊤ ⊤ d₁ h₁₂).ofInjective (iotaDeg_injective M₁ M₂ ⊤ ⊤ d₁ h₁₂)) x)))
    rw [MulEquiv.symm_apply_apply]
    rfl

private theorem corner_q2_one_aux {N q : ℕ} [NeZero N] [NeZero q] (A : Type) [AddCommGroup A]
    (hqp : q.Prime) (hqN : ¬ q ∣ N)
    (hb1 : LevelLE N (N * q) (⊤ : Subgroup (ZMod N)ˣ) (⊤ : Subgroup (ZMod (N * q))ˣ) 1)
    (hbq : LevelLE N (N * q) (⊤ : Subgroup (ZMod N)ˣ) (⊤ : Subgroup (ZMod (N * q))ˣ) q)
    {M₃ : ℕ} [NeZero M₃] (hM₃ : M₃ = N * q * q) {d : ℕ} [NeZero d] (hd : d = q * q)
    (hi1 : LevelLE (N * q) M₃ (⊤ : Subgroup (ZMod (N * q))ˣ) (⊤ : Subgroup (ZMod M₃)ˣ) 1)
    (hiq : LevelLE (N * q) M₃ (⊤ : Subgroup (ZMod (N * q))ˣ) (⊤ : Subgroup (ZMod M₃)ˣ) q)
    (h1 : LevelLE N M₃ (⊤ : Subgroup (ZMod N)ˣ) (⊤ : Subgroup (ZMod M₃)ˣ) 1)
    (hqq : LevelLE N M₃ (⊤ : Subgroup (ZMod N)ˣ) (⊤ : Subgroup (ZMod M₃)ˣ) d)
    (φ : H1 N ⊤ A) :
    jDeg N M₃ ⊤ ⊤ d A hqq (iDeg' N M₃ ⊤ ⊤ 1 A h1 φ)
      = heckeT N ⊤ q A (heckeT N ⊤ q A φ) - ((q : ℤ) + 1) • φ := by
  subst hM₃
  subst hd

  rw [iDeg_comp_eq (d₁ := 1) (d₂ := 1) (Nat.one_mul 1).symm hb1 hi1 h1 A φ]

  rw [jDeg_comp_eq (d₁ := q) (d₂ := q) rfl hbq hiq hqq A]

  rw [CohCarrier.jDeg_iDeg_cross_eq_index_smul_heckeT q hiq hi1
      (dvd_refl (q : ℤ)) (Nat.one_mul q).symm,
    subgroupOf_rangeIotaQ_index_one hiq, one_smul]

  rw [CohCarrier.heckeT_iDeg_interchange hqp hqN hb1 hbq φ]

  rw [AddMonoidHom.map_sub]

  rw [CohCarrier.jDeg_iDeg_cross_eq_index_smul_heckeT q hbq hb1
      (dvd_refl (q : ℤ)) (Nat.one_mul q).symm,
    subgroupOf_rangeIotaQ_index_one hbq, one_smul]

  rw [CohCarrier.jDeg_comp_iDegP_self hbq φ, rangeIotaQ_eq_upper hbq,
    CohCarrier.index_GammaHUpper_of_prime N ⊤ q hqp hqN]

  have hcast : ((q : ℤ) + 1) • φ = (q + 1) • φ := by
    rw [show ((q : ℤ) + 1) = ((q + 1 : ℕ) : ℤ) by push_cast; ring, natCast_zsmul]
  rw [hcast]

private theorem entry_dvd_of_mem {M' : ℕ} (γ' : ↥(GammaH M' ⊤)) :
    ((M' : ℕ) : ℤ) ∣ (γ' : SL(2, ℤ)) 1 0 := by
  obtain ⟨hA, -⟩ := mem_GammaH_iff.mp γ'.2
  rw [CongruenceSubgroup.Gamma0_mem] at hA
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hA

private theorem rangeIotaOne_eq_lower {N ℓ : ℕ} [NeZero N] [NeZero ℓ]
    (h : LevelLE N (N * ℓ) (⊤ : Subgroup (ZMod N)ˣ) (⊤ : Subgroup (ZMod (N * ℓ))ˣ) 1) :
    (iotaDeg N (N * ℓ) ⊤ ⊤ 1 h).range = GammaHLower N ⊤ ℓ := by
  apply le_antisymm
  · rintro x ⟨γ', rfl⟩
    rw [Subgroup.mem_subgroupOf, CongruenceSubgroup.Gamma0_mem, CohCarrier.coe_iotaDeg_one h γ',
      ZMod.intCast_zmod_eq_zero_iff_dvd, Nat.mul_comm ℓ N]
    exact entry_dvd_of_mem γ'
  · intro g hg
    rw [Subgroup.mem_subgroupOf, CongruenceSubgroup.Gamma0_mem, ZMod.intCast_zmod_eq_zero_iff_dvd, Nat.mul_comm ℓ N] at hg
    refine ⟨⟨(g : ↥(GammaH N ⊤)), ?_⟩, ?_⟩
    · rw [GammaH_top, CongruenceSubgroup.Gamma0_mem, ZMod.intCast_zmod_eq_zero_iff_dvd]
      exact hg
    · apply Subtype.ext
      exact CohCarrier.coe_iotaDeg_one h _

private theorem subgroupOf_rangeIotaOne_lower_index_one {N ℓ : ℕ} [NeZero N] [NeZero ℓ]
    (h : LevelLE N (N * ℓ) (⊤ : Subgroup (ZMod N)ˣ) (⊤ : Subgroup (ZMod (N * ℓ))ˣ) 1) :
    ((iotaDeg N (N * ℓ) ⊤ ⊤ 1 h).range.subgroupOf (GammaHLower N ⊤ ℓ)).index = 1 := by
  rw [rangeIotaOne_eq_lower h, Subgroup.subgroupOf_self, Subgroup.index_top]

private theorem levelLE_N_Nq_one (N q : ℕ) :
    LevelLE N (N * q) (⊤ : Subgroup (ZMod N)ˣ) (⊤ : Subgroup (ZMod (N * q))ˣ) 1 :=
  ⟨dvd_mul_right N q, one_dvd _, fun _ _ => Subgroup.mem_top _⟩

private theorem levelLE_N_Nq_q (N q : ℕ) [NeZero N] :
    LevelLE N (N * q) (⊤ : Subgroup (ZMod N)ˣ) (⊤ : Subgroup (ZMod (N * q))ˣ) q := by
  refine ⟨dvd_mul_right N q, ?_, fun _ _ => Subgroup.mem_top _⟩
  rw [Nat.mul_div_cancel_left q (Nat.pos_of_ne_zero (NeZero.ne N))]

private theorem levelLE_Nq_Nq2_one (N q : ℕ) :
    LevelLE (N * q) (N * q ^ 2) (⊤ : Subgroup (ZMod (N * q))ˣ) (⊤ : Subgroup (ZMod (N * q ^ 2))ˣ) 1 :=
  ⟨⟨q, by ring⟩, one_dvd _, fun _ _ => Subgroup.mem_top _⟩

private theorem levelLE_Nq_Nq2_q (N q : ℕ) [NeZero N] [NeZero q] :
    LevelLE (N * q) (N * q ^ 2) (⊤ : Subgroup (ZMod (N * q))ˣ) (⊤ : Subgroup (ZMod (N * q ^ 2))ˣ) q := by
  refine ⟨⟨q, by ring⟩, ?_, fun _ _ => Subgroup.mem_top _⟩
  have hpos : 0 < N * q := Nat.pos_of_ne_zero (mul_ne_zero (NeZero.ne N) (NeZero.ne q))
  rw [show N * q ^ 2 = N * q * q by ring, Nat.mul_div_cancel_left q hpos]

private theorem corner_q2_one {N q : ℕ} [NeZero N] [NeZero q] (A : Type) [AddCommGroup A]
    (hq : q.Prime) (hqN : ¬ q ∣ N)
    (h1 : LevelLE N (N * q ^ 2) (⊤ : Subgroup (ZMod N)ˣ) (⊤ : Subgroup (ZMod (N * q ^ 2))ˣ) 1)
    (hq2 : LevelLE N (N * q ^ 2) (⊤ : Subgroup (ZMod N)ˣ) (⊤ : Subgroup (ZMod (N * q ^ 2))ˣ) (q ^ 2))
    (φ : H1 N ⊤ A) :
    jDeg N (N * q ^ 2) ⊤ ⊤ (q ^ 2) A hq2 (iDeg' N (N * q ^ 2) ⊤ ⊤ 1 A h1 φ)
      = heckeT N ⊤ q A (heckeT N ⊤ q A φ) - ((q : ℤ) + 1) • φ :=
  corner_q2_one_aux A hq hqN (levelLE_N_Nq_one N q) (levelLE_N_Nq_q N q) (by ring) (sq q)
    (levelLE_Nq_Nq2_one N q) (levelLE_Nq_Nq2_q N q) h1 hq2 φ

private theorem corner_one_q2 {N q : ℕ} [NeZero N] [NeZero q] (A : Type) [AddCommGroup A]
    (hq : q.Prime) (hqN : ¬ q ∣ N)
    (h1 : LevelLE N (N * q ^ 2) (⊤ : Subgroup (ZMod N)ˣ) (⊤ : Subgroup (ZMod (N * q ^ 2))ˣ) 1)
    (hq2 : LevelLE N (N * q ^ 2) (⊤ : Subgroup (ZMod N)ˣ) (⊤ : Subgroup (ZMod (N * q ^ 2))ˣ) (q ^ 2))
    (φ : H1 N ⊤ A) :
    jDeg N (N * q ^ 2) ⊤ ⊤ 1 A h1 (iDeg' N (N * q ^ 2) ⊤ ⊤ (q ^ 2) A hq2 φ)
      = heckeT N ⊤ q A (heckeT N ⊤ q A φ) - ((q : ℤ) + 1) • φ := by
  have hcop : Nat.Coprime (q ^ 2) N := Nat.Coprime.pow_left 2 ((hq.coprime_iff_not_dvd).mpr hqN)

  rw [jDeg_iDeg_cross_eq_index_smul_heckeTlower_of_coprime hcop h1 hq2
      (Int.natCast_dvd_natCast.mpr (Dvd.intro_left N (by ring))) (Nat.one_mul (q ^ 2)).symm φ,
    subgroupOf_rangeIotaOne_lower_index_one h1, one_smul,
    heckeSym_top_of_coprime N (q ^ 2) hcop φ]

  have hU := CohCarrier.jDeg_iDeg_cross_eq_index_smul_heckeT (q ^ 2) hq2 h1 (dvd_refl _)
    (Nat.one_mul (q ^ 2)).symm φ
  rw [subgroupOf_rangeIotaQ_index_one hq2, one_smul] at hU
  rw [← hU]
  exact corner_q2_one A hq hqN h1 hq2 φ

end IharaSolCorner

open CohCarrier IharaSolCorner in

theorem solution (N q : ℕ) [NeZero N] [NeZero q]
    (A : Type) [AddCommGroup A] (hq : q.Prime) (hqN : ¬ q ∣ N)
    (h1 : LevelLE N (N * q ^ 2) (⊤ : Subgroup (ZMod N)ˣ) (⊤ : Subgroup (ZMod (N * q ^ 2))ˣ) 1)
    (hq2 : LevelLE N (N * q ^ 2) (⊤ : Subgroup (ZMod N)ˣ)
      (⊤ : Subgroup (ZMod (N * q ^ 2))ˣ) (q ^ 2)) :
    (∀ φ, (jDeg N (N*q^2) ⊤ ⊤ 1 A h1).comp (iDeg' N (N*q^2) ⊤ ⊤ (q^2) A hq2) φ
        = (heckeT N ⊤ q A).comp (heckeT N ⊤ q A) φ - ((q : ℤ) + 1) • φ) ∧
    (∀ φ, (jDeg N (N*q^2) ⊤ ⊤ (q^2) A hq2).comp (iDeg' N (N*q^2) ⊤ ⊤ 1 A h1) φ
        = (heckeT N ⊤ q A).comp (heckeT N ⊤ q A) φ - ((q : ℤ) + 1) • φ) := by
  refine ⟨fun φ => ?_, fun φ => ?_⟩
  · simp only [AddMonoidHom.comp_apply]
    exact corner_one_q2 A hq hqN h1 hq2 φ
  · simp only [AddMonoidHom.comp_apply]
    exact corner_q2_one A hq hqN h1 hq2 φ

#print axioms solution

end S_CohCarrier_jDeg_iDeg_corner_of_prime_sq
end P2MW
export P2MW.S_CohCarrier_jDeg_iDeg_corner_of_prime_sq (solution)
