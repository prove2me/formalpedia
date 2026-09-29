-- Prove2me | solution 1 for CuspForm.exists_isPrimitiveForm_basis_gammaH_and_heckeTLinH_and_diamondLinH_and_heckeULinH_apply
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/99bdc4a3-459b-51c8-ba87-aa27cc3eda42

import Definitions.Def_CuspForm_HeckeOperatorFormsGammaH
import Definitions.Def_CuspForm_PrimitiveFormGamma1
import Mathlib.NumberTheory.DirichletCharacter.Orthogonality
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Theorems.Thm_CuspForm_exists_isPrimitiveForm_linearIndependent_degeneracy_and_mem_span_of_hasNebentypus
import Theorems.Thm_CuspForm_exists_finset_dirichlet_sum_eq_and_independent_of_gammaH
import Theorems.Thm_CuspForm_exists_gamma1_coe_eq_of_gammaH
import Theorems.Thm_CuspForm_exists_gammaH_coe_eq_of_hasNebentypus
import Theorems.Thm_CuspForm_coe_diamondLinH_and_coe_heckeTLinH_and_coe_heckeULinH_of_hasNebentypus
import Theorems.Thm_CuspForm_IsEigenformWith_heckeU_add_smul_slash_heckeDiagMatrix_degeneracy_eq_qCoeff_smul
import Theorems.Thm_CuspForm_IsEigenformWith_heckeU_degeneracy_of_dvd_level
import Theorems.Thm_ModularFormClass_eq_of_forall_qCoeff_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CuspForm_exists_isPrimitiveForm_basis_gammaH_and_heckeTLinH_and_diamondLinH_and_heckeULinH_apply
p2m_attr_erase "instance" "FLT.HyperbolicMeasure.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatIntUpperHalfPlaneVolume_definitions FLT.HyperbolicMeasure.instIsOpenPosMeasureUpperHalfPlaneVolume_definitions FLT.Gamma0FundamentalSet.instContinuousConstSMulSpecialLinearGroupFinOfNatNatIntUpperHalfPlane_definitions FLT.L2ProductionInstance.isFiniteMeasure_gamma0 FLT.L2ProductionInstance.countable_SL2Z FLT.L2ProductionInstance.countable_quotient FLT.L2ProductionInstance.nontrivial_gamma0L2 Ihara.instGroupIharaAmalgam"
p2m_attr_erase "simp" "FreyPackage.ModMCarrier.coe_rescaleLin_apply ModularForm.AtkinLehnerDatum.mk.injEq ModularForm.AtkinLehnerDatum.alGL_coe ModularForm.AtkinLehnerDatum.mk.sizeOf_spec ModularForm.AtkinLehnerDatum.sqUnitSL_coe ModularForm.AtkinLehnerDatum.det_sqUnit ModularForm.AtkinLehnerDatum.det_mat FLT.TruncatedDomainPartition.unipotentDiagonalSum_zero Ihara.wConj_coe Ihara.wConj_symm_coe Ihara.coe_iota1 Ihara.coe_iota1SL Ihara.iota1Mat_apply_one_zero Ihara.iota1Mat_apply_zero_zero Ihara.iota1Mat_apply_zero_one Ihara.iota1Mat_apply_one_one Ihara.coe_iota0 Ihara.iharaEdge_one Ihara.pairFamily_zero Ihara.iharaEdge_zero Ihara.pairFamily_one Ihara.coe_amalgamToGamma0Away Ihara.coe_vertexZero Ihara.coe_slToAway CuspForm.Gamma1Hecke.redMatrix_apply_one_one CuspForm.Gamma1Hecke.redMatrix_apply_one_zero CuspForm.Gamma1Hecke.lift_infty CuspForm.Gamma1Hecke.heckeRep_infty CuspForm.Gamma1Hecke.heckeRep_coe CuspForm.Gamma1Hecke.wt_infty CuspForm.Gamma1Hecke.redMatrix_apply_zero_one CuspForm.coe_slashLinOfMemGamma0_apply CuspForm.Gamma1Hecke.wt_coe CuspForm.Gamma1Hecke.lift_coe CuspForm.Gamma1Hecke.redMatrix_apply_zero_zero CuspForm.coe_heckeTOne CuspForm.coe_heckeTLinOne_apply CuspForm.coe_slashOfMemGamma0 CuspForm.PeterssonCoset.mapGL_apply"

set_option autoImplicit false
set_option maxHeartbeats 6400000

noncomputable section

open scoped MatrixGroups ModularForm
open CongruenceSubgroup ModularFormClass

namespace DCMP

variable (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) (k : ℤ)

theorem one_mem_strictPeriods_Gamma1 (N : ℕ) :
    (1 : ℝ) ∈ ((Gamma1 N : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by
  simp

theorem denom_eq (A : SL(2, ℤ)) (τ : UpperHalfPlane) :
    UpperHalfPlane.denom (A : GL (Fin 2) ℝ) τ = ((A 1 0 : ℤ) : ℂ) * (τ : ℂ) + ((A 1 1 : ℤ) : ℂ) := by
  simp [UpperHalfPlane.denom]

variable {M k}

theorem slash_eq_smul_of_hasNebentypus {ε : DirichletCharacter ℂ M}
    {g : CuspForm (Gamma1 M) k} (hg : CuspForm.HasNebentypus ε g)
    (A : SL(2, ℤ)) (hA0 : A ∈ Gamma0 M) :
    (⇑g) ∣[k] ((Matrix.SpecialLinearGroup.mapGL ℝ A : GL (Fin 2) ℝ)) = ε ((A 1 1 : ℤ) : ZMod M) • ⇑g := by
  funext τ
  show ((⇑g) ∣[k] A) τ = _
  rw [ModularForm.SL_slash_apply, hg A hA0 τ, Pi.smul_apply, smul_eq_mul]
  have hne : ((A 1 0 : ℤ) : ℂ) * (τ : ℂ) + ((A 1 1 : ℤ) : ℂ) ≠ 0 := by
    rw [← denom_eq]; exact UpperHalfPlane.denom_ne_zero _ _
  rw [denom_eq, mul_assoc, mul_assoc, mul_comm (_ ^ k), mul_assoc, ← zpow_add₀ hne, neg_add_cancel,
    zpow_zero, mul_one]

theorem hasNebentypus_of_slash_eq_smul {ε : DirichletCharacter ℂ M}
    {g : CuspForm (Gamma1 M) k} {F : UpperHalfPlane → ℂ} (hF : F = ⇑g)
    (h : ∀ σ : Gamma0 M, F ∣[k] ((Matrix.SpecialLinearGroup.mapGL ℝ (σ : SL(2, ℤ)) : GL (Fin 2) ℝ)) =
      ε (((σ : SL(2, ℤ)) 1 1 : ℤ) : ZMod M) • F) :
    CuspForm.HasNebentypus ε g := by
  intro A hA0 τ
  have := congrFun (h ⟨A, hA0⟩) τ
  rw [hF] at this
  change ((⇑g) ∣[k] A) τ = _ at this
  rw [ModularForm.SL_slash_apply, Pi.smul_apply, smul_eq_mul, denom_eq] at this
  have hne : ((A 1 0 : ℤ) : ℂ) * (τ : ℂ) + ((A 1 1 : ℤ) : ℂ) ≠ 0 := by
    rw [← denom_eq]; exact UpperHalfPlane.denom_ne_zero _ _
  have hz : (((A 1 0 : ℤ) : ℂ) * (τ : ℂ) + ((A 1 1 : ℤ) : ℂ)) ^ (-k) ≠ 0 := zpow_ne_zero _ hne

  have := congrArg (fun z => z * (((A 1 0 : ℤ) : ℂ) * (τ : ℂ) + ((A 1 1 : ℤ) : ℂ)) ^ k) this
  simp only at this
  rw [mul_assoc, ← zpow_add₀ hne, neg_add_cancel, zpow_zero, mul_one] at this
  rw [this]; ring

end DCMP

namespace DCMP

variable {M : ℕ} [NeZero M] {k : ℤ}

theorem nebentypus_unique {L : ℕ} [NeZero L] {ε₁ ε₂ : DirichletCharacter ℂ L} {g : CuspForm (Gamma1 L) k}
    (hg : g ≠ 0) (h₁ : CuspForm.HasNebentypus ε₁ g) (h₂ : CuspForm.HasNebentypus ε₂ g) : ε₁ = ε₂ := by
  have hτ : ∃ τ : UpperHalfPlane, g τ ≠ 0 := by
    by_contra h
    push Not at h
    exact hg (DFunLike.ext _ _ h)
  obtain ⟨τ, hτ⟩ := hτ
  apply MulChar.ext
  intro u
  obtain ⟨γ, hγ⟩ := CohCarrier.gamma0Units_surjective L u
  have e1 := h₁ (γ : SL(2, ℤ)) γ.2 τ
  have e2 := h₂ (γ : SL(2, ℤ)) γ.2 τ
  rw [e1] at e2
  have hd : (((γ : SL(2, ℤ)) 1 1 : ℤ) : ZMod L) = (u : ZMod L) := by
    rw [← hγ, CohCarrier.val_gamma0Units]; rfl
  rw [hd] at e2
  have hne : ((((γ : SL(2, ℤ)) 1 0 : ℤ) : ℂ) * (τ : ℂ) + (((γ : SL(2, ℤ)) 1 1 : ℤ) : ℂ)) ^ k * g τ ≠ 0 := by
    refine mul_ne_zero (zpow_ne_zero _ ?_) hτ
    rw [← denom_eq]; exact UpperHalfPlane.denom_ne_zero _ _
  exact mul_right_cancel₀ hne e2

variable (M k)

structure Dat where
  n : DirichletCharacter ℂ M → ℕ
  L : (ε : DirichletCharacter ℂ M) → Fin (n ε) → ℕ
  hL : ∀ ε i, L ε i ∣ M
  chr : (ε : DirichletCharacter ℂ M) → (i : Fin (n ε)) → DirichletCharacter ℂ (L ε i)
  g : (ε : DirichletCharacter ℂ M) → (i : Fin (n ε)) → CuspForm (Gamma1 (L ε i)) k
  G : (ε : DirichletCharacter ℂ M) → Fin (n ε) → ℕ → CuspForm (Gamma1 M) k
  hprim : ∀ ε i, CuspForm.IsPrimitiveForm (chr ε i) (g ε i)
  hdist : ∀ ε i j, i ≠ j → L ε i ≠ L ε j ∨ ∃ m : ℕ, qCoeff (g ε i) m ≠ qCoeff (g ε j) m
  hch : ∀ ε i, DirichletCharacter.changeLevel (hL ε i) (chr ε i) = ε
  hG : ∀ ε i (d : ℕ), d ∣ M / L ε i →
    (∀ τ : UpperHalfPlane, G ε i d τ = g ε i (ModularForm.heckeDiagMatrix d • τ)) ∧
    CuspForm.HasNebentypus ε (G ε i d)
  hli : ∀ ε, LinearIndependent ℂ (fun x : (Σ i : Fin (n ε), ↥(Nat.divisors (M / L ε i))) => G ε x.1 (x.2 : ℕ))
  hspan : ∀ ε (f : CuspForm (Gamma1 M) k), CuspForm.HasNebentypus ε f →
    f ∈ Submodule.span ℂ (Set.range fun x : (Σ i : Fin (n ε), ↥(Nat.divisors (M / L ε i))) => G ε x.1 (x.2 : ℕ))

theorem nonempty_dat : Nonempty (Dat M k) := by
  choose n L hL chr g G hprim hdist hch _hcomp hG hli hspan using
    fun ε : DirichletCharacter ℂ M =>
      CuspForm.exists_isPrimitiveForm_linearIndependent_degeneracy_and_mem_span_of_hasNebentypus M k ε
  exact ⟨⟨n, L, hL, chr, g, G, hprim, hdist, hch, hG, hli, hspan⟩⟩

variable {M k}
variable (H : Subgroup (ZMod M)ˣ) (𝒟 : Dat M k)

def EH : Finset (DirichletCharacter ℂ M) := by
  classical
  exact Finset.univ.filter (fun ε => ∀ u : (ZMod M)ˣ, u ∈ H → ε (u : ZMod M) = 1)

theorem mem_EH {ε : DirichletCharacter ℂ M} : ε ∈ EH H ↔ ∀ u : (ZMod M)ˣ, u ∈ H → ε (u : ZMod M) = 1 := by
  classical
  simp [EH]

abbrev Idx : Type := Σ ε : ↥(EH H), Fin (𝒟.n (ε : DirichletCharacter ℂ M))

abbrev chrOf (x : Idx H 𝒟) : DirichletCharacter ℂ M := (x.1 : DirichletCharacter ℂ M)
abbrev LOf (x : Idx H 𝒟) : ℕ := 𝒟.L (chrOf H 𝒟 x) x.2

theorem chrOf_mem (x : Idx H 𝒟) : ∀ u : (ZMod M)ˣ, u ∈ H → chrOf H 𝒟 x (u : ZMod M) = 1 :=
  (mem_EH H).mp x.1.2

def GH (x : Idx H 𝒟) (d : ℕ) : CuspForm (CohCarrier.GammaH M H) k :=
  if hd : d ∣ M / LOf H 𝒟 x then
    Classical.choose (CuspForm.exists_gammaH_coe_eq_of_hasNebentypus M H k (chrOf H 𝒟 x) (chrOf_mem H 𝒟 x)
      (𝒟.G (chrOf H 𝒟 x) x.2 d) ((𝒟.hG (chrOf H 𝒟 x) x.2 d hd).2))
  else 0

theorem coe_GH (x : Idx H 𝒟) {d : ℕ} (hd : d ∣ M / LOf H 𝒟 x) :
    (⇑(GH H 𝒟 x d) : UpperHalfPlane → ℂ) = ⇑(𝒟.G (chrOf H 𝒟 x) x.2 d) := by
  rw [GH, dif_pos hd]
  exact Classical.choose_spec (CuspForm.exists_gammaH_coe_eq_of_hasNebentypus M H k (chrOf H 𝒟 x)
    (chrOf_mem H 𝒟 x) (𝒟.G (chrOf H 𝒟 x) x.2 d) ((𝒟.hG (chrOf H 𝒟 x) x.2 d hd).2))

theorem LOf_ne_zero (x : Idx H 𝒟) : LOf H 𝒟 x ≠ 0 := fun h => by
  have := 𝒟.hL (chrOf H 𝒟 x) x.2; rw [show 𝒟.L (chrOf H 𝒟 x) x.2 = 0 from h, zero_dvd_iff] at this
  exact NeZero.ne M this

theorem div_ne_zero (x : Idx H 𝒟) : M / LOf H 𝒟 x ≠ 0 :=
  Nat.ne_of_gt (Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne M)) (𝒟.hL _ _))
    (Nat.pos_of_ne_zero (LOf_ne_zero H 𝒟 x)))

theorem dist (x y : Idx H 𝒟) (hxy : x ≠ y) :
    LOf H 𝒟 x ≠ LOf H 𝒟 y ∨ ∃ m : ℕ, qCoeff (𝒟.g (chrOf H 𝒟 x) x.2) m ≠ qCoeff (𝒟.g (chrOf H 𝒟 y) y.2) m := by
  obtain ⟨ε, i⟩ := x
  obtain ⟨ε', j⟩ := y
  by_cases hε : ε = ε'
  · subst hε
    have hij : i ≠ j := fun h => hxy (by subst h; rfl)
    exact 𝒟.hdist _ i j hij
  ·
    by_contra h
    push Not at h
    obtain ⟨hL, hq⟩ := h
    apply hε
    apply Subtype.ext

    change 𝒟.L (ε : DirichletCharacter ℂ M) i = 𝒟.L (ε' : DirichletCharacter ℂ M) j at hL
    have key : ∀ (L₁ : ℕ) (h₁ : L₁ ∣ M) (c₁ : DirichletCharacter ℂ L₁) (g₁ : CuspForm (Gamma1 L₁) k)
        (L₂ : ℕ) (h₂ : L₂ ∣ M) (c₂ : DirichletCharacter ℂ L₂) (g₂ : CuspForm (Gamma1 L₂) k),
        CuspForm.IsPrimitiveForm c₁ g₁ → CuspForm.IsPrimitiveForm c₂ g₂ → L₁ = L₂ →
        (∀ m : ℕ, qCoeff g₁ m = qCoeff g₂ m) →
        DirichletCharacter.changeLevel h₁ c₁ = DirichletCharacter.changeLevel h₂ c₂ := by
      intro L₁ h₁ c₁ g₁ L₂ h₂ c₂ g₂ hp₁ hp₂ hL12 hq12
      subst hL12
      haveI : NeZero L₁ := ⟨fun h => by rw [h, zero_dvd_iff] at h₁; exact NeZero.ne M h₁⟩
      have hg : g₁ = g₂ := ModularFormClass.eq_of_forall_qCoeff_eq (one_mem_strictPeriods_Gamma1 L₁) hq12
      subst hg
      have hne : g₁ ≠ 0 := by
        intro h0
        have := hp₁.isEigenformWith.qCoeff_one
        rw [h0] at this
        simp [qCoeff, UpperHalfPlane.qExpansion_zero] at this
      rw [nebentypus_unique hne hp₁.isEigenformWith.hasNebentypus hp₂.isEigenformWith.hasNebentypus]
    have := key _ (𝒟.hL _ i) _ _ _ (𝒟.hL _ j) _ _ (𝒟.hprim _ i) (𝒟.hprim _ j) hL hq
    rwa [𝒟.hch, 𝒟.hch] at this

end DCMP

namespace DCMP

variable {M : ℕ} [NeZero M] {k : ℤ} (H : Subgroup (ZMod M)ˣ) (𝒟 : Dat M k)

theorem hasNebentypus_zero {N : ℕ} (ε : DirichletCharacter ℂ N) :
    CuspForm.HasNebentypus ε (0 : CuspForm (Gamma1 N) k) := by
  intro γ _ τ; simp

theorem hasNebentypus_add {N : ℕ} {ε : DirichletCharacter ℂ N} {f g : CuspForm (Gamma1 N) k}
    (hf : CuspForm.HasNebentypus ε f) (hg : CuspForm.HasNebentypus ε g) :
    CuspForm.HasNebentypus ε (f + g) := by
  intro γ hγ τ
  simp only [CuspForm.add_apply, hf γ hγ τ, hg γ hγ τ]
  ring

theorem hasNebentypus_smul {N : ℕ} {ε : DirichletCharacter ℂ N} {f : CuspForm (Gamma1 N) k} (c : ℂ)
    (hf : CuspForm.HasNebentypus ε f) : CuspForm.HasNebentypus ε (c • f) := by
  intro γ hγ τ
  simp only [CuspForm.IsGLPos.smul_apply, smul_eq_mul, hf γ hγ τ]
  ring

theorem hasNebentypus_sum {N : ℕ} {ε : DirichletCharacter ℂ N} {ι : Type*} (s : Finset ι)
    (f : ι → CuspForm (Gamma1 N) k) (hf : ∀ i ∈ s, CuspForm.HasNebentypus ε (f i)) :
    CuspForm.HasNebentypus ε (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hasNebentypus_zero ε
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact hasNebentypus_add (hf a (Finset.mem_insert_self a s))
      (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

theorem coe_sum {Γ : Subgroup (GL (Fin 2) ℝ)} {ι : Type*} (s : Finset ι) (f : ι → CuspForm Γ k) :
    (⇑(∑ i ∈ s, f i) : UpperHalfPlane → ℂ) = ∑ i ∈ s, ⇑(f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, CuspForm.coe_add, ih]

def Fof (c : (Σ x : Idx H 𝒟, ↥(Nat.divisors (M / LOf H 𝒟 x))) → ℂ) (e : ↥(EH H)) : CuspForm (Gamma1 M) k :=
  ∑ i : Fin (𝒟.n (e : DirichletCharacter ℂ M)),
    ∑ dd : ↥(Nat.divisors (M / 𝒟.L (e : DirichletCharacter ℂ M) i)),
      c ⟨⟨e, i⟩, dd⟩ • 𝒟.G (e : DirichletCharacter ℂ M) i (dd : ℕ)

theorem hasNebentypus_Fof (c : (Σ x : Idx H 𝒟, ↥(Nat.divisors (M / LOf H 𝒟 x))) → ℂ) (e : ↥(EH H)) :
    CuspForm.HasNebentypus (e : DirichletCharacter ℂ M) (Fof H 𝒟 c e) := by
  unfold Fof
  refine hasNebentypus_sum _ _ fun i _ => hasNebentypus_sum _ _ fun dd _ => hasNebentypus_smul _ ?_
  exact (𝒟.hG _ i dd (Nat.dvd_of_mem_divisors dd.2)).2

theorem linearIndependent :
    LinearIndependent ℂ (fun y : (Σ x : Idx H 𝒟, ↥(Nat.divisors (M / LOf H 𝒟 x))) => GH H 𝒟 y.1 (y.2 : ℕ)) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro c hc y

  let gB : DirichletCharacter ℂ M → CuspForm (CohCarrier.GammaH M H) k := fun ε =>
    if h : ε ∈ EH H then
      Classical.choose (CuspForm.exists_gammaH_coe_eq_of_hasNebentypus M H k ε ((mem_EH H).mp h)
        (Fof H 𝒟 c ⟨ε, h⟩) (hasNebentypus_Fof H 𝒟 c ⟨ε, h⟩))
    else 0
  have hgB : ∀ (ε) (h : ε ∈ EH H), (⇑(gB ε) : UpperHalfPlane → ℂ) = ⇑(Fof H 𝒟 c ⟨ε, h⟩) := by
    intro ε h
    simp only [gB, dif_pos h]
    exact Classical.choose_spec (CuspForm.exists_gammaH_coe_eq_of_hasNebentypus M H k ε ((mem_EH H).mp h)
      (Fof H 𝒟 c ⟨ε, h⟩) (hasNebentypus_Fof H 𝒟 c ⟨ε, h⟩))
  have hslash : ∀ ε ∈ EH H, ∀ σ : Gamma0 M,
      ⇑(gB ε) ∣[k] ((Matrix.SpecialLinearGroup.mapGL ℝ (σ : SL(2, ℤ)) : GL (Fin 2) ℝ)) =
        ε (((σ : SL(2, ℤ)) 1 1 : ℤ) : ZMod M) • ⇑(gB ε) := by
    intro ε h σ
    rw [hgB ε h]
    exact slash_eq_smul_of_hasNebentypus (hasNebentypus_Fof H 𝒟 c ⟨ε, h⟩) _ σ.2
  have hsum0 : (∑ ε ∈ EH H, ⇑(gB ε)) = 0 := by
    have h1 : (∑ ε ∈ EH H, ⇑(gB ε)) = ∑ e : ↥(EH H), ⇑(Fof H 𝒟 c e) := by
      rw [← Finset.sum_coe_sort]
      exact Finset.sum_congr rfl fun e _ => hgB e e.2
    have h2 : (⇑(∑ y, c y • GH H 𝒟 y.1 (y.2 : ℕ)) : UpperHalfPlane → ℂ) =
        ∑ y, c y • ⇑(𝒟.G (chrOf H 𝒟 y.1) y.1.2 (y.2 : ℕ)) := by
      rw [coe_sum Finset.univ (fun y : (Σ x : Idx H 𝒟, ↥(Nat.divisors (M / LOf H 𝒟 x))) =>
        c y • GH H 𝒟 y.1 (y.2 : ℕ))]
      exact Finset.sum_congr rfl fun y _ => by
        rw [CuspForm.IsGLPos.coe_smul, coe_GH H 𝒟 y.1 (Nat.dvd_of_mem_divisors y.2.2)]
    have h3 : (∑ e : ↥(EH H), (⇑(Fof H 𝒟 c e) : UpperHalfPlane → ℂ)) =
        ∑ y, c y • ⇑(𝒟.G (chrOf H 𝒟 y.1) y.1.2 (y.2 : ℕ)) := by
      simp only [Fof, coe_sum, CuspForm.IsGLPos.coe_smul, Fintype.sum_sigma]
    rw [h1, h3, ← h2, hc, CuspForm.coe_zero]
  have hB := (CuspForm.exists_finset_dirichlet_sum_eq_and_independent_of_gammaH M H k).2 (EH H) gB hslash hsum0

  have hF : ∀ e : ↥(EH H), Fof H 𝒟 c e = 0 := by
    intro e
    apply DFunLike.ext'
    rw [← hgB e e.2, hB e e.2]
    rfl

  obtain ⟨⟨e, i⟩, dd⟩ := y
  have hli := (Fintype.linearIndependent_iff.mp (𝒟.hli (e : DirichletCharacter ℂ M)))
    (fun z => c ⟨⟨e, z.1⟩, z.2⟩) ?_ ⟨i, dd⟩
  · exact hli
  · have := hF e
    rw [Fof] at this
    simpa only [Fintype.sum_sigma] using this

theorem mem_span (f : CuspForm (CohCarrier.GammaH M H) k) :
    f ∈ Submodule.span ℂ (Set.range fun y : (Σ x : Idx H 𝒟, ↥(Nat.divisors (M / LOf H 𝒟 x))) =>
      GH H 𝒟 y.1 (y.2 : ℕ)) := by
  classical
  obtain ⟨s, fε, hH, hslash, hsum⟩ := (CuspForm.exists_finset_dirichlet_sum_eq_and_independent_of_gammaH M H k).1 f
  have hf : f = ∑ ε ∈ s, fε ε := by
    apply DFunLike.ext'
    rw [coe_sum]; exact hsum
  rw [hf]
  refine Submodule.sum_mem _ fun ε hε => ?_

  obtain ⟨g₁, hg₁⟩ := CuspForm.exists_gamma1_coe_eq_of_gammaH M H k (fε ε)
  have hneb : CuspForm.HasNebentypus ε g₁ := hasNebentypus_of_slash_eq_smul hg₁.symm (hslash ε hε)
  let e : ↥(EH H) := ⟨ε, (mem_EH H).mpr (hH ε hε)⟩
  have hsp := 𝒟.hspan ε g₁ hneb
  rw [Submodule.mem_span_range_iff_exists_fun] at hsp
  obtain ⟨a, ha⟩ := hsp
  have hfe : fε ε = ∑ z : (Σ i : Fin (𝒟.n ε), ↥(Nat.divisors (M / 𝒟.L ε i))), a z • GH H 𝒟 ⟨e, z.1⟩ (z.2 : ℕ) := by
    apply DFunLike.ext'
    rw [coe_sum, ← hg₁, ← ha, coe_sum]
    refine Finset.sum_congr rfl fun z _ => ?_
    rw [CuspForm.IsGLPos.coe_smul, CuspForm.IsGLPos.coe_smul, coe_GH H 𝒟 ⟨e, z.1⟩ (Nat.dvd_of_mem_divisors z.2.2)]
  rw [hfe]
  refine Submodule.sum_mem _ fun z _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨⟨e, z.1⟩, z.2⟩, rfl⟩)

end DCMP

namespace DCMP

variable {M : ℕ} [NeZero M] {k : ℤ} (H : Subgroup (ZMod M)ˣ) (𝒟 : Dat M k)

theorem chr_natCast_eq (x : Idx H 𝒟) {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ M) :
    chrOf H 𝒟 x (ℓ : ZMod M) = 𝒟.chr (chrOf H 𝒟 x) x.2 (ℓ : ZMod (LOf H 𝒟 x)) := by
  have hu : IsUnit (ℓ : ZMod M) := (ZMod.isUnit_prime_iff_not_dvd hℓ).mpr hℓM
  have := congrArg (fun χ : DirichletCharacter ℂ M => χ (hu.unit : ZMod M)) (𝒟.hch (chrOf H 𝒟 x) x.2)
  rw [DirichletCharacter.changeLevel_eq_cast_of_dvd, IsUnit.unit_spec, ZMod.cast_natCast (𝒟.hL _ _)] at this
  exact this.symm

theorem heckeT_GH {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ M) (x : Idx H 𝒟) {d : ℕ} (hd : d ∣ M / LOf H 𝒟 x) :
    haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
    CuspForm.heckeTLinH k hℓ hℓM (GH H 𝒟 x d) = qCoeff (𝒟.g (chrOf H 𝒟 x) x.2) ℓ • GH H 𝒟 x d := by
  haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
  haveI : NeZero (LOf H 𝒟 x) := ⟨LOf_ne_zero H 𝒟 x⟩
  have hG := 𝒟.hG (chrOf H 𝒟 x) x.2
  have hM2c := (CuspForm.coe_diamondLinH_and_coe_heckeTLinH_and_coe_heckeULinH_of_hasNebentypus M H k
    (chrOf H 𝒟 x) (GH H 𝒟 x d) (𝒟.G (chrOf H 𝒟 x) x.2 d) (coe_GH H 𝒟 x hd) (hG d hd).2).2.1 ℓ hℓ hℓM
  have hM4b := CuspForm.IsEigenformWith.heckeU_add_smul_slash_heckeDiagMatrix_degeneracy_eq_qCoeff_smul M k
    (𝒟.hL _ _) (𝒟.hprim (chrOf H 𝒟 x) x.2).isEigenformWith (𝒟.G (chrOf H 𝒟 x) x.2)
    (fun d hd => (hG d hd).1) hℓ hℓM hd
  apply DFunLike.ext'
  change (⇑(CuspForm.heckeTLinH k hℓ hℓM (GH H 𝒟 x d)) : UpperHalfPlane → ℂ) = ⇑(_ • GH H 𝒟 x d)
  rw [hM2c, CuspForm.IsGLPos.coe_smul, coe_GH H 𝒟 x hd, ← hM4b, chr_natCast_eq H 𝒟 x hℓ hℓM]

theorem diamond_GH (u : (ZMod M)ˣ) (x : Idx H 𝒟) {d : ℕ} (hd : d ∣ M / LOf H 𝒟 x) :
    CuspForm.diamondLinH k u (GH H 𝒟 x d) =
      DirichletCharacter.changeLevel (𝒟.hL _ _) (𝒟.chr (chrOf H 𝒟 x) x.2) (u : ZMod M) • GH H 𝒟 x d := by
  have hG := 𝒟.hG (chrOf H 𝒟 x) x.2
  have hM2c := (CuspForm.coe_diamondLinH_and_coe_heckeTLinH_and_coe_heckeULinH_of_hasNebentypus M H k
    (chrOf H 𝒟 x) (GH H 𝒟 x d) (𝒟.G (chrOf H 𝒟 x) x.2 d) (coe_GH H 𝒟 x hd) (hG d hd).2).1 u
  apply DFunLike.ext'
  change (⇑(CuspForm.diamondLinH k u (GH H 𝒟 x d)) : UpperHalfPlane → ℂ) = ⇑(_ • GH H 𝒟 x d)
  rw [hM2c, CuspForm.IsGLPos.coe_smul, coe_GH H 𝒟 x hd, 𝒟.hch]

theorem mul_dvd_div {q : ℕ} (hq : q.Prime) (hqM : q ∣ M) (x : Idx H 𝒟) (hqL : ¬ q ∣ LOf H 𝒟 x) {d : ℕ}
    (hd : d ∣ M / LOf H 𝒟 x) (hqd : ¬ q ∣ d) : d * q ∣ M / LOf H 𝒟 x := by
  have hcop : Nat.Coprime d q := Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd hq).mpr hqd)
  refine hcop.mul_dvd_of_dvd_of_dvd hd ?_
  have hqML : Nat.Coprime q (LOf H 𝒟 x) := (Nat.Prime.coprime_iff_not_dvd hq).mpr hqL
  have : q ∣ LOf H 𝒟 x * (M / LOf H 𝒟 x) := by rw [Nat.mul_div_cancel' (𝒟.hL _ _)]; exact hqM
  exact hqML.dvd_of_dvd_mul_left this

theorem heckeU_GH {q : ℕ} (hq : q.Prime) (hqM : q ∣ M) (x : Idx H 𝒟) {d : ℕ} (hd : d ∣ M / LOf H 𝒟 x) :
    (q ∣ d → CuspForm.heckeULinH k q (GH H 𝒟 x d) = GH H 𝒟 x (d / q)) ∧
    (¬ q ∣ d → q ∣ LOf H 𝒟 x → CuspForm.heckeULinH k q (GH H 𝒟 x d) =
      qCoeff (𝒟.g (chrOf H 𝒟 x) x.2) q • GH H 𝒟 x d) ∧
    (¬ q ∣ d → ¬ q ∣ LOf H 𝒟 x → CuspForm.heckeULinH k q (GH H 𝒟 x d) =
      qCoeff (𝒟.g (chrOf H 𝒟 x) x.2) q • GH H 𝒟 x d -
        (𝒟.chr (chrOf H 𝒟 x) x.2 (q : ZMod (LOf H 𝒟 x)) * (q : ℂ) ^ (k - 1)) • GH H 𝒟 x (d * q)) := by
  haveI : NeZero (LOf H 𝒟 x) := ⟨LOf_ne_zero H 𝒟 x⟩
  have hG := 𝒟.hG (chrOf H 𝒟 x) x.2
  have hM2c := (CuspForm.coe_diamondLinH_and_coe_heckeTLinH_and_coe_heckeULinH_of_hasNebentypus M H k
    (chrOf H 𝒟 x) (GH H 𝒟 x d) (𝒟.G (chrOf H 𝒟 x) x.2 d) (coe_GH H 𝒟 x hd) (hG d hd).2).2.2 q hq hqM
  have hM4c := CuspForm.IsEigenformWith.heckeU_degeneracy_of_dvd_level M k (𝒟.hL _ _)
    (𝒟.hprim (chrOf H 𝒟 x) x.2).isEigenformWith (𝒟.G (chrOf H 𝒟 x) x.2) (fun d hd => (hG d hd).1) hq hqM hd
  refine ⟨fun hqd => ?_, fun hqd hqL => ?_, fun hqd hqL => ?_⟩
  · apply DFunLike.ext'
    change (⇑(CuspForm.heckeULinH k q (GH H 𝒟 x d)) : UpperHalfPlane → ℂ) = ⇑(GH H 𝒟 x (d / q))
    rw [hM2c, hM4c.1 hqd, coe_GH H 𝒟 x ((Nat.div_dvd_of_dvd hqd).trans hd)]
  · apply DFunLike.ext'
    change (⇑(CuspForm.heckeULinH k q (GH H 𝒟 x d)) : UpperHalfPlane → ℂ) = ⇑(_ • GH H 𝒟 x d)
    rw [hM2c, hM4c.2.1 hqd hqL, CuspForm.IsGLPos.coe_smul, coe_GH H 𝒟 x hd]
  · apply DFunLike.ext'
    change (⇑(CuspForm.heckeULinH k q (GH H 𝒟 x d)) : UpperHalfPlane → ℂ) = ⇑(_ • GH H 𝒟 x d - _ • GH H 𝒟 x (d * q))
    rw [hM2c, hM4c.2.2 hqd hqL, CuspForm.coe_sub, CuspForm.IsGLPos.coe_smul, CuspForm.IsGLPos.coe_smul,
      coe_GH H 𝒟 x hd, coe_GH H 𝒟 x (mul_dvd_div H 𝒟 hq hqM x hqL hd hqd)]

theorem main (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) (k : ℤ) :
    ∃ (n : ℕ) (L : Fin n → ℕ) (hL : ∀ i, L i ∣ M)
      (ε : (i : Fin n) → DirichletCharacter ℂ (L i))
      (g : (i : Fin n) → CuspForm (CongruenceSubgroup.Gamma1 (L i)) k)
      (G : Fin n → ℕ → CuspForm (CohCarrier.GammaH M H) k),
      (∀ i, CuspForm.IsPrimitiveForm (ε i) (g i)) ∧
      (∀ i j, i ≠ j → L i ≠ L j ∨ ∃ m : ℕ, ModularFormClass.qCoeff (g i) m ≠ ModularFormClass.qCoeff (g j) m) ∧
      (∀ i, ∀ u : (ZMod M)ˣ, u ∈ H → DirichletCharacter.changeLevel (hL i) (ε i) (u : ZMod M) = 1) ∧
      (∀ (i : Fin n) (d : ℕ), d ∣ M / L i →
        ∀ τ : UpperHalfPlane, G i d τ = g i (ModularForm.heckeDiagMatrix d • τ)) ∧
      LinearIndependent ℂ (fun x : (Σ i : Fin n, ↥(Nat.divisors (M / L i))) => G x.1 (x.2 : ℕ)) ∧
      Submodule.span ℂ (Set.range fun x : (Σ i : Fin n, ↥(Nat.divisors (M / L i))) => G x.1 (x.2 : ℕ)) = ⊤ ∧
      (∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ M) (i : Fin n) (d : ℕ), d ∣ M / L i →
        haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
        CuspForm.heckeTLinH k hℓ hℓM (G i d) = ModularFormClass.qCoeff (g i) ℓ • G i d) ∧
      (∀ (u : (ZMod M)ˣ) (i : Fin n) (d : ℕ), d ∣ M / L i →
        CuspForm.diamondLinH k u (G i d) = DirichletCharacter.changeLevel (hL i) (ε i) (u : ZMod M) • G i d) ∧
      (∀ (q : ℕ), q.Prime → q ∣ M → ∀ (i : Fin n) (d : ℕ), d ∣ M / L i →
        (q ∣ d → CuspForm.heckeULinH k q (G i d) = G i (d / q)) ∧
        (¬ q ∣ d → q ∣ L i → CuspForm.heckeULinH k q (G i d) = ModularFormClass.qCoeff (g i) q • G i d) ∧
        (¬ q ∣ d → ¬ q ∣ L i → CuspForm.heckeULinH k q (G i d) =
          ModularFormClass.qCoeff (g i) q • G i d - (ε i (q : ZMod (L i)) * (q : ℂ) ^ (k - 1)) • G i (d * q))) := by
  classical
  obtain ⟨𝒟⟩ := nonempty_dat M k
  let N : ℕ := Fintype.card (Idx H 𝒟)
  let e : Idx H 𝒟 ≃ Fin N := Fintype.equivFin _
  let X : Fin N → Idx H 𝒟 := fun y => e.symm y
  have hXinj : Function.Injective X := e.symm.injective
  refine ⟨N, fun y => LOf H 𝒟 (X y), fun y => 𝒟.hL _ _, fun y => 𝒟.chr (chrOf H 𝒟 (X y)) (X y).2,
    fun y => 𝒟.g (chrOf H 𝒟 (X y)) (X y).2, fun y d => GH H 𝒟 (X y) d,
    fun y => 𝒟.hprim _ _, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i j hij
    exact dist H 𝒟 (X i) (X j) (fun h => hij (hXinj h))
  · intro i u hu
    rw [𝒟.hch]
    exact chrOf_mem H 𝒟 (X i) u hu
  · intro i d hd τ
    rw [coe_GH H 𝒟 (X i) hd]
    exact (𝒟.hG _ _ d hd).1 τ
  ·
    have h := linearIndependent H 𝒟
    let σ : (Σ y : Fin N, ↥(Nat.divisors (M / LOf H 𝒟 (X y)))) ≃
        (Σ x : Idx H 𝒟, ↥(Nat.divisors (M / LOf H 𝒟 x))) := Equiv.sigmaCongrLeft (β := fun x : Idx H 𝒟 => ↥(Nat.divisors (M / LOf H 𝒟 x))) e.symm
    have : (fun z : (Σ y : Fin N, ↥(Nat.divisors (M / LOf H 𝒟 (X y)))) => GH H 𝒟 (X z.1) (z.2 : ℕ)) =
        (fun w : (Σ x : Idx H 𝒟, ↥(Nat.divisors (M / LOf H 𝒟 x))) => GH H 𝒟 w.1 (w.2 : ℕ)) ∘ σ := by
      funext z; rfl
    rw [this, linearIndependent_equiv]
    exact h
  · apply top_unique
    intro f _
    have hf := mem_span H 𝒟 f
    let σ : (Σ y : Fin N, ↥(Nat.divisors (M / LOf H 𝒟 (X y)))) ≃
        (Σ x : Idx H 𝒟, ↥(Nat.divisors (M / LOf H 𝒟 x))) := Equiv.sigmaCongrLeft (β := fun x : Idx H 𝒟 => ↥(Nat.divisors (M / LOf H 𝒟 x))) e.symm
    have : (Set.range fun z : (Σ y : Fin N, ↥(Nat.divisors (M / LOf H 𝒟 (X y)))) => GH H 𝒟 (X z.1) (z.2 : ℕ)) =
        Set.range fun w : (Σ x : Idx H 𝒟, ↥(Nat.divisors (M / LOf H 𝒟 x))) => GH H 𝒟 w.1 (w.2 : ℕ) := by
      have hc : (fun z : (Σ y : Fin N, ↥(Nat.divisors (M / LOf H 𝒟 (X y)))) => GH H 𝒟 (X z.1) (z.2 : ℕ)) =
          (fun w : (Σ x : Idx H 𝒟, ↥(Nat.divisors (M / LOf H 𝒟 x))) => GH H 𝒟 w.1 (w.2 : ℕ)) ∘ σ := by
        funext z; rfl
      rw [hc, EquivLike.range_comp]
    rw [this]
    exact hf
  · intro ℓ hℓ hℓM i d hd
    exact heckeT_GH H 𝒟 hℓ hℓM (X i) hd
  · intro u i d hd
    exact diamond_GH H 𝒟 u (X i) hd
  · intro q hq hqM i d hd
    exact heckeU_GH H 𝒟 hq hqM (X i) hd

end DCMP

end

theorem solution
    (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) (k : ℤ) :
    ∃ (n : ℕ) (L : Fin n → ℕ) (hL : ∀ i, L i ∣ M)
      (ε : (i : Fin n) → DirichletCharacter ℂ (L i))
      (g : (i : Fin n) → CuspForm (CongruenceSubgroup.Gamma1 (L i)) k)
      (G : Fin n → ℕ → CuspForm (CohCarrier.GammaH M H) k),
      (∀ i, CuspForm.IsPrimitiveForm (ε i) (g i)) ∧
      (∀ i j, i ≠ j → L i ≠ L j ∨ ∃ m : ℕ, ModularFormClass.qCoeff (g i) m ≠ ModularFormClass.qCoeff (g j) m) ∧
      (∀ i, ∀ u : (ZMod M)ˣ, u ∈ H → DirichletCharacter.changeLevel (hL i) (ε i) (u : ZMod M) = 1) ∧
      (∀ (i : Fin n) (d : ℕ), d ∣ M / L i →
        ∀ τ : UpperHalfPlane, G i d τ = g i (ModularForm.heckeDiagMatrix d • τ)) ∧
      LinearIndependent ℂ (fun x : (Σ i : Fin n, ↥(Nat.divisors (M / L i))) => G x.1 (x.2 : ℕ)) ∧
      Submodule.span ℂ (Set.range fun x : (Σ i : Fin n, ↥(Nat.divisors (M / L i))) => G x.1 (x.2 : ℕ)) = ⊤ ∧
      (∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ M) (i : Fin n) (d : ℕ), d ∣ M / L i →
        haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
        CuspForm.heckeTLinH k hℓ hℓM (G i d) = ModularFormClass.qCoeff (g i) ℓ • G i d) ∧
      (∀ (u : (ZMod M)ˣ) (i : Fin n) (d : ℕ), d ∣ M / L i →
        CuspForm.diamondLinH k u (G i d) = DirichletCharacter.changeLevel (hL i) (ε i) (u : ZMod M) • G i d) ∧
      (∀ (q : ℕ), q.Prime → q ∣ M → ∀ (i : Fin n) (d : ℕ), d ∣ M / L i →
        (q ∣ d → CuspForm.heckeULinH k q (G i d) = G i (d / q)) ∧
        (¬ q ∣ d → q ∣ L i → CuspForm.heckeULinH k q (G i d) = ModularFormClass.qCoeff (g i) q • G i d) ∧
        (¬ q ∣ d → ¬ q ∣ L i → CuspForm.heckeULinH k q (G i d) =
          ModularFormClass.qCoeff (g i) q • G i d - (ε i (q : ZMod (L i)) * (q : ℂ) ^ (k - 1)) • G i (d * q))) :=
  DCMP.main M H k

end S_CuspForm_exists_isPrimitiveForm_basis_gammaH_and_heckeTLinH_and_diamondLinH_and_heckeULinH_apply
end P2MW
export P2MW.S_CuspForm_exists_isPrimitiveForm_basis_gammaH_and_heckeTLinH_and_diamondLinH_and_heckeULinH_apply (solution)
