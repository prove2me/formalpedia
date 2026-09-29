-- Prove2me | solution 1 for CuspForm.exists_isEigenformWith_qCoeff_eq_of_heckeTLinH_eq_smul_of_heckeULinH_eq_smul_of_diamondLinH_eq_smul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/af2816d4-0877-5030-ad80-0678cec3d4fe

import Mathlib
import Definitions.Def_CuspForm_HeckeOperatorFormsGammaH
import Definitions.Def_CuspForm_PrimitiveFormGamma1
import Definitions.Def_CuspForm_Gamma1HeckeOperators
import Theorems.Thm_CuspForm_heckeTLinH_heckeULinH_diamondLinH_comm
import Theorems.Thm_CuspForm_heckeULinH_comm
import Theorems.Thm_CuspForm_stableU
import Theorems.Thm_CuspForm_stableT
import Theorems.Thm_CuspForm_stableD
import Theorems.Thm_CuspForm_exists_gamma1_coe_eq_of_gammaH
import Theorems.Thm_CuspForm_coe_diamondLinH_and_coe_heckeTLinH_and_coe_heckeULinH_of_hasNebentypus
import Theorems.Thm_CuspForm_qCoeff_one_ne_zero_and_isEigenformWith_smul_of_hasNebentypus_of_qCoeff_hecke_eigen_forall
import Theorems.Thm_CuspForm_exists_isPrimitiveForm_basis_gammaH_and_heckeTLinH_and_diamondLinH_and_heckeULinH_apply
import Theorems.Thm_CuspForm_qCoeff_heckeTLinOne
import Theorems.Thm_CuspForm_HasNebentypus_diamondLinOne_apply_eq_smul
import Theorems.Thm_ModularFormClass_qCoeff_heckeU
import Theorems.Thm_Module_End_exists_common_eigenvector_of_commute
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CuspForm_exists_isEigenformWith_qCoeff_eq_of_heckeTLinH_eq_smul_of_heckeULinH_eq_smul_of_diamondLinH_eq_smul
p2m_attr_erase "instance" "FLT.HyperbolicMeasure.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatIntUpperHalfPlaneVolume_definitions FLT.HyperbolicMeasure.instIsOpenPosMeasureUpperHalfPlaneVolume_definitions FLT.Gamma0FundamentalSet.instContinuousConstSMulSpecialLinearGroupFinOfNatNatIntUpperHalfPlane_definitions FLT.L2ProductionInstance.isFiniteMeasure_gamma0 FLT.L2ProductionInstance.countable_SL2Z FLT.L2ProductionInstance.countable_quotient FLT.L2ProductionInstance.nontrivial_gamma0L2 Ihara.instGroupIharaAmalgam"
p2m_attr_erase "simp" "FreyPackage.ModMCarrier.coe_rescaleLin_apply ModularForm.AtkinLehnerDatum.mk.injEq ModularForm.AtkinLehnerDatum.alGL_coe ModularForm.AtkinLehnerDatum.mk.sizeOf_spec ModularForm.AtkinLehnerDatum.sqUnitSL_coe ModularForm.AtkinLehnerDatum.det_sqUnit ModularForm.AtkinLehnerDatum.det_mat FLT.TruncatedDomainPartition.unipotentDiagonalSum_zero Ihara.wConj_coe Ihara.wConj_symm_coe Ihara.coe_iota1 Ihara.coe_iota1SL Ihara.iota1Mat_apply_one_zero Ihara.iota1Mat_apply_zero_zero Ihara.iota1Mat_apply_zero_one Ihara.iota1Mat_apply_one_one Ihara.coe_iota0 Ihara.iharaEdge_one Ihara.pairFamily_zero Ihara.iharaEdge_zero Ihara.pairFamily_one Ihara.coe_amalgamToGamma0Away Ihara.coe_vertexZero Ihara.coe_slToAway CuspForm.PeterssonCoset.mapGL_apply"

set_option autoImplicit false

noncomputable section

open scoped MatrixGroups ModularForm
open CongruenceSubgroup ModularFormClass UpperHalfPlane

namespace Ws41
namespace FormsU

theorem finset_sum_slash {ι : Type*} (s : Finset ι) (k : ℤ) (g : GL (Fin 2) ℝ) (F : ι → ℍ → ℂ) :
    (∑ i ∈ s, F i) ∣[k] g = ∑ i ∈ s, (F i) ∣[k] g := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [SlashAction.zero_slash]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, SlashAction.add_slash, ih]

theorem heckeMatrix_one_zero : ModularForm.heckeMatrix 1 0 = 1 := by
  ext i j : 2
  rw [ModularForm.val_heckeMatrix one_ne_zero]
  fin_cases i <;> fin_cases j <;> simp

theorem heckeU_one (k : ℤ) (f : ℍ → ℂ) : ModularForm.heckeU k 1 f = f := by
  rw [ModularForm.heckeU_def, Finset.sum_range_one, heckeMatrix_one_zero, SlashAction.slash_one]

theorem heckeMatrix_mul_heckeMatrix {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) (i j : ℕ) :
    ModularForm.heckeMatrix b j * ModularForm.heckeMatrix a i =
      ModularForm.heckeMatrix (a * b) (i + a * j) := by
  ext r c : 2
  rw [Units.val_mul, ModularForm.val_heckeMatrix hb, ModularForm.val_heckeMatrix ha,
    ModularForm.val_heckeMatrix (mul_ne_zero ha hb)]
  fin_cases r <;> fin_cases c <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring

theorem sum_range_mul_eq {A : Type*} [AddCommMonoid A] {a : ℕ} (ha : a ≠ 0) (b : ℕ) (F : ℕ → A) :
    ∑ m ∈ Finset.range (a * b), F m = ∑ i ∈ Finset.range a, ∑ j ∈ Finset.range b, F (i + a * j) := by
  rw [← Finset.sum_product']
  refine Finset.sum_nbij' (fun m => (m % a, m / a)) (fun p => p.1 + a * p.2) ?_ ?_ ?_ ?_ ?_
  · intro m hm
    simp only [Finset.mem_range, Finset.mem_product] at hm ⊢
    exact ⟨Nat.mod_lt _ (Nat.pos_of_ne_zero ha), (Nat.div_lt_iff_lt_mul (Nat.pos_of_ne_zero ha)).2 (by rwa [mul_comm] at hm)⟩
  · intro p hp
    simp only [Finset.mem_range, Finset.mem_product] at hp ⊢
    calc p.1 + a * p.2 < a + a * p.2 := by omega
      _ = a * (p.2 + 1) := by ring
      _ ≤ a * b := Nat.mul_le_mul_left _ hp.2
  · intro m _
    exact Nat.mod_add_div m a
  · intro p hp
    simp only [Finset.mem_range, Finset.mem_product] at hp
    ext
    · show (p.1 + a * p.2) % a = p.1
      rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hp.1]
    · show (p.1 + a * p.2) / a = p.2
      rw [Nat.add_mul_div_left _ _ (Nat.pos_of_ne_zero ha), Nat.div_eq_of_lt hp.1, zero_add]
  · intro m _
    rw [Nat.mod_add_div]

theorem heckeU_mul (k : ℤ) (a b : ℕ) (f : ℍ → ℂ) :
    ModularForm.heckeU k (a * b) f = ModularForm.heckeU k a (ModularForm.heckeU k b f) := by
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · simp [ModularForm.heckeU_zero_left]
  rcases Nat.eq_zero_or_pos b with rfl | hb
  · simp [ModularForm.heckeU_zero_left, ModularForm.heckeU_zero]
  rw [ModularForm.heckeU_def, ModularForm.heckeU_def, sum_range_mul_eq ha.ne' b]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [ModularForm.heckeU_def, finset_sum_slash]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← SlashAction.slash_mul, heckeMatrix_mul_heckeMatrix ha.ne' hb.ne']

section GammaH

variable {M : ℕ} [NeZero M] {H : Subgroup (ZMod M)ˣ} {k : ℤ}

local notation "SkH" => CuspForm (CohCarrier.GammaH M H) k

theorem stableU_of_forall_exists (q : ℕ)
    (h : ∀ f : SkH, ∃ g : SkH, ModularForm.heckeU k q ⇑f = ⇑g) : CuspForm.StableU M H k q := by
  intro f
  obtain ⟨g, hg⟩ := h f
  rw [hg]
  exact ⟨fun γ hγ => SlashInvariantFormClass.slash_action_eq g γ hγ, g.holo',
    fun c hc => CuspForm.zero_at_cusps' g hc⟩

theorem stableU_of_dvd : ∀ q : ℕ, q ∣ M → CuspForm.StableU M H k q := by
  intro q
  induction q using Nat.strong_induction_on with
  | _ q ih =>
    intro hqM
    have hq0 : q ≠ 0 := fun h => (NeZero.ne M) (Nat.eq_zero_of_zero_dvd (h ▸ hqM))
    by_cases hq1 : q = 1
    · subst hq1
      exact stableU_of_forall_exists 1 fun f => ⟨f, heckeU_one k ⇑f⟩
    · have hp : q.minFac.Prime := Nat.minFac_prime hq1
      set p := q.minFac with hpdef
      have hpq : p ∣ q := Nat.minFac_dvd q
      obtain ⟨m, hm⟩ := hpq
      have hm0 : m ≠ 0 := by rintro rfl; exact hq0 (by rw [hm, mul_zero])
      have hmlt : m < q := by
        rw [hm]; exact lt_mul_of_one_lt_left (Nat.pos_of_ne_zero hm0) hp.one_lt
      have hmM : m ∣ M := Nat.dvd_trans (Dvd.intro_left p hm.symm) hqM
      have hpM : p ∣ M := Nat.dvd_trans (Dvd.intro m hm.symm) hqM
      have hUm : CuspForm.StableU M H k m := ih m hmlt hmM
      have hUp : CuspForm.StableU M H k p := CuspForm.stableU M H k hp hpM
      refine stableU_of_forall_exists q fun f => ⟨CuspForm.heckeULinH k p (CuspForm.heckeULinH k m f), ?_⟩
      rw [hm, heckeU_mul, CuspForm.coe_heckeULinH_apply k hUp, CuspForm.coe_heckeULinH_apply k hUm]

theorem coe_heckeULinH_of_dvd {q : ℕ} (hq : q ∣ M) (f : SkH) :
    ⇑(CuspForm.heckeULinH k q f) = ModularForm.heckeU k q ⇑f :=
  CuspForm.coe_heckeULinH_apply k (stableU_of_dvd q hq) f

theorem heckeULinH_one (f : SkH) : CuspForm.heckeULinH k 1 f = f :=
  DFunLike.coe_fn_eq.mp <| by rw [coe_heckeULinH_of_dvd (one_dvd M), heckeU_one]

theorem heckeULinH_mul {a b : ℕ} (hab : a * b ∣ M) (f : SkH) :
    CuspForm.heckeULinH k (a * b) f = CuspForm.heckeULinH k a (CuspForm.heckeULinH k b f) :=
  DFunLike.coe_fn_eq.mp <| by
    rw [coe_heckeULinH_of_dvd hab, coe_heckeULinH_of_dvd (Nat.dvd_trans (Dvd.intro b rfl) hab),
      coe_heckeULinH_of_dvd (Nat.dvd_trans (Dvd.intro_left a rfl) hab), heckeU_mul]

theorem comm_heckeULinH_of_prime (A : SkH →ₗ[ℂ] SkH)
    (hA : ∀ p : ℕ, p.Prime → p ∣ M → ∀ f : SkH,
      A (CuspForm.heckeULinH k p f) = CuspForm.heckeULinH k p (A f)) :
    ∀ q : ℕ, q ∣ M → ∀ f : SkH, A (CuspForm.heckeULinH k q f) = CuspForm.heckeULinH k q (A f) := by
  intro q
  induction q using Nat.strong_induction_on with
  | _ q ih =>
    intro hqM f
    have hq0 : q ≠ 0 := fun h => (NeZero.ne M) (Nat.eq_zero_of_zero_dvd (h ▸ hqM))
    by_cases hq1 : q = 1
    · subst hq1; rw [heckeULinH_one, heckeULinH_one]
    · have hp : q.minFac.Prime := Nat.minFac_prime hq1
      obtain ⟨m, hm⟩ := (Nat.minFac_dvd q : q.minFac ∣ q)
      have hm0 : m ≠ 0 := by rintro rfl; exact hq0 (by rw [hm, mul_zero])
      have hmlt : m < q := by
        rw [hm]; exact lt_mul_of_one_lt_left (Nat.pos_of_ne_zero hm0) hp.one_lt
      have hqM' : q.minFac * m ∣ M := hm ▸ hqM
      have hmM : m ∣ M := Nat.dvd_trans (Dvd.intro_left _ rfl) hqM'
      have hpM : q.minFac ∣ M := Nat.dvd_trans (Dvd.intro m rfl) hqM'
      rw [hm, heckeULinH_mul hqM', heckeULinH_mul hqM', hA _ hp hpM, ih m hmlt hmM]

abbrev Idx (M : ℕ) : Type := {ℓ : ℕ // ℓ.Prime ∧ ¬ ℓ ∣ M} ⊕ {p : ℕ // p.Prime ∧ p ∣ M} ⊕ (ZMod M)ˣ

def op (k : ℤ) : Idx M → (CuspForm (CohCarrier.GammaH M H) k →ₗ[ℂ] CuspForm (CohCarrier.GammaH M H) k)
  | Sum.inl ℓ => CuspForm.heckeTLinH k ℓ.2.1 ℓ.2.2
  | Sum.inr (Sum.inl p) => CuspForm.heckeULinH k p.1
  | Sum.inr (Sum.inr u) => CuspForm.diamondLinH k u

theorem op_comm_T (i : Idx M) {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ M) (g : SkH) :
    op (H := H) k i (CuspForm.heckeTLinH k hℓ hℓM g) = CuspForm.heckeTLinH k hℓ hℓM (op k i g) := by
  obtain ⟨hTT, hTU, hTD, hUD, hDD⟩ := CuspForm.heckeTLinH_heckeULinH_diamondLinH_comm M H k
  rcases i with ℓ' | p | u
  · exact hTT _ _ ℓ'.2.1 ℓ'.2.2 hℓ hℓM g
  · exact (hTU ℓ hℓ hℓM p.1 p.2.1 p.2.2 g).symm
  · exact (hTD ℓ hℓ hℓM u g).symm

theorem op_comm_Uprime (i : Idx M) {p : ℕ} (hp : p.Prime) (hpM : p ∣ M) (g : SkH) :
    op (H := H) k i (CuspForm.heckeULinH k p g) = CuspForm.heckeULinH k p (op k i g) := by
  obtain ⟨hTT, hTU, hTD, hUD, hDD⟩ := CuspForm.heckeTLinH_heckeULinH_diamondLinH_comm M H k
  rcases i with ℓ' | p' | u
  · exact hTU _ ℓ'.2.1 ℓ'.2.2 p hp hpM g
  · exact CuspForm.heckeULinH_comm M H k p'.2.1 p'.2.2 hp hpM g
  · exact (hUD p hp hpM u g).symm

theorem op_comm_U (i : Idx M) {q : ℕ} (hq : q ∣ M) (g : SkH) :
    op (H := H) k i (CuspForm.heckeULinH k q g) = CuspForm.heckeULinH k q (op k i g) :=
  comm_heckeULinH_of_prime (op k i) (fun _ hp hpM g => op_comm_Uprime i hp hpM g) q hq g

theorem op_comm_D (i : Idx M) (u : (ZMod M)ˣ) (g : SkH) :
    op (H := H) k i (CuspForm.diamondLinH k u g) = CuspForm.diamondLinH k u (op k i g) := by
  obtain ⟨hTT, hTU, hTD, hUD, hDD⟩ := CuspForm.heckeTLinH_heckeULinH_diamondLinH_comm M H k
  rcases i with ℓ' | p | u'
  · exact hTD _ ℓ'.2.1 ℓ'.2.2 u g
  · exact hUD p.1 p.2.1 p.2.2 u g
  · exact hDD u' u g

theorem op_comm (i j : Idx M) (g : SkH) : op (H := H) k i (op k j g) = op k j (op k i g) := by
  rcases j with ℓ | p | u
  · exact op_comm_T i ℓ.2.1 ℓ.2.2 g
  · exact op_comm_Uprime i p.2.1 p.2.2 g
  · exact op_comm_D i u g

def jointEig (k : ℤ) (S Q : Set ℕ) (a b : ℕ → ℂ) (e : (ZMod M)ˣ →* ℂˣ) :
    Submodule ℂ (CuspForm (CohCarrier.GammaH M H) k) :=
  (⨅ (ℓ : ℕ) (hℓ : ℓ.Prime) (_ : ℓ ∉ S) (hℓM : ¬ ℓ ∣ M),
      Module.End.eigenspace (CuspForm.heckeTLinH (H := H) k hℓ hℓM) (a ℓ)) ⊓
  (⨅ (q : ℕ) (_ : q ∈ Q), Module.End.eigenspace (CuspForm.heckeULinH (H := H) k q) (b q)) ⊓
  (⨅ u : (ZMod M)ˣ, Module.End.eigenspace (CuspForm.diamondLinH (H := H) k u) (e u : ℂ))

theorem mem_jointEig_iff {S Q : Set ℕ} {a b : ℕ → ℂ} {e : (ZMod M)ˣ →* ℂˣ} {g : SkH} :
    g ∈ jointEig k S Q a b e ↔
      (∀ (ℓ : ℕ) (hℓ : ℓ.Prime), ℓ ∉ S → ∀ hℓM : ¬ ℓ ∣ M, CuspForm.heckeTLinH k hℓ hℓM g = a ℓ • g) ∧
      (∀ q ∈ Q, CuspForm.heckeULinH k q g = b q • g) ∧
      (∀ u : (ZMod M)ˣ, CuspForm.diamondLinH k u g = (e u : ℂ) • g) := by
  simp only [jointEig, Submodule.mem_inf, Submodule.mem_iInf, Module.End.mem_eigenspace_iff, and_assoc]

theorem op_mem_jointEig {S Q : Set ℕ} {a b : ℕ → ℂ} {e : (ZMod M)ˣ →* ℂˣ}
    (hQ : ∀ q ∈ Q, q ∣ M) (i : Idx M) {g : SkH} (hg : g ∈ jointEig k S Q a b e) :
    op k i g ∈ jointEig k S Q a b e := by
  rw [mem_jointEig_iff] at hg ⊢
  obtain ⟨h1, h2, h3⟩ := hg
  refine ⟨fun ℓ hℓ hℓS hℓM => ?_, fun q hq => ?_, fun u => ?_⟩
  · rw [← op_comm_T, h1 ℓ hℓ hℓS hℓM, map_smul]
  · rw [← op_comm_U i (hQ q hq), h2 q hq, map_smul]
  · rw [← op_comm_D, h3 u, map_smul]

theorem finiteDimensional_gammaH : FiniteDimensional ℂ (CuspForm (CohCarrier.GammaH M H) k) := by
  obtain ⟨n, L, hL, ε, g, G, -, -, -, -, -, hspan, -⟩ :=
    CuspForm.exists_isPrimitiveForm_basis_gammaH_and_heckeTLinH_and_diamondLinH_and_heckeULinH_apply M H k
  exact Module.finite_def.mpr (Submodule.fg_def.mpr ⟨_, Set.finite_range _, hspan⟩)

theorem hasNebentypus_of_diamond (e : (ZMod M)ˣ →* ℂˣ) (f₀ : SkH)
    (hD : ∀ u : (ZMod M)ˣ, CuspForm.diamondLinH k u f₀ = (e u : ℂ) • f₀)
    (g : CuspForm (Gamma1 M) k) (hg : (⇑g : ℍ → ℂ) = ⇑f₀) :
    CuspForm.HasNebentypus (MulChar.ofUnitHom e : DirichletCharacter ℂ M) g := by
  intro γ hγ τ
  set u : (ZMod M)ˣ := CohCarrier.gamma0Units M ⟨γ, hγ⟩ with hu
  have hεu : (MulChar.ofUnitHom e : DirichletCharacter ℂ M) ((γ 1 1 : ℤ) : ZMod M) = e u := by
    rw [show (((γ 1 1 : ℤ) : ZMod M)) = (u : ZMod M) from rfl, MulChar.ofUnitHom_coe]
  have h1 : ⇑(CuspForm.diamondLinH k u f₀) =
      ⇑f₀ ∣[k] ((Matrix.SpecialLinearGroup.mapGL ℝ ((⟨γ, hγ⟩ : Gamma0 M) : SL(2, ℤ)) : GL (Fin 2) ℝ)) :=
    CuspForm.coe_diamondLinH_eq_slash k (CuspForm.stableD M H k) u ⟨γ, hγ⟩ rfl f₀
  rw [hD u] at h1
  have h2 : ((e u : ℂ) • ⇑f₀) τ = (⇑f₀ ∣[k] γ) τ := by
    have := congr_fun h1 τ
    exact this
  have hne : (((γ 1 0 : ℤ) : ℂ) * (τ : ℂ) + ((γ 1 1 : ℤ) : ℂ)) ≠ 0 := by
    rw [← ModularGroup.denom_apply]; exact denom_ne_zero _ _
  rw [ModularForm.SL_slash_apply, Pi.smul_apply, smul_eq_mul, ModularGroup.denom_apply, zpow_neg,
    eq_mul_inv_iff_mul_eq₀ (zpow_ne_zero k hne)] at h2
  rw [hg, hεu, ← h2]
  ring

end GammaH

section GammaOne

variable {M : ℕ} {k : ℤ}

theorem one_mem_strictPeriods_Gamma1 : (1 : ℝ) ∈ (Gamma1 M : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by
  simp

theorem qCoeff_smul (c : ℂ) (g : CuspForm (Gamma1 M) k) (n : ℕ) :
    qCoeff (⇑(c • g)) n = c * qCoeff (⇑g) n := by
  unfold qCoeff
  rw [CuspForm.IsGLPos.coe_smul, ModularForm.qExpansion_smul one_pos one_mem_strictPeriods_Gamma1 c g,
    map_smul, smul_eq_mul]

theorem qCoeff_smul' (c : ℂ) (g : CuspForm (Gamma1 M) k) (n : ℕ) :
    qCoeff (c • ⇑g) n = c * qCoeff (⇑g) n := by
  rw [← CuspForm.IsGLPos.coe_smul, qCoeff_smul]

theorem qrel_T (g : CuspForm (Gamma1 M) k) (ε : DirichletCharacter ℂ M) (hε : CuspForm.HasNebentypus ε g)
    {p : ℕ} (hp : p.Prime) (hpM : ¬ p ∣ M) (c : ℂ)
    (hTp : ModularForm.heckeU k p ⇑g + ε (p : ZMod M) • ((⇑g) ∣[k] ModularForm.heckeDiagMatrix p) = c • ⇑g)
    (n : ℕ) :
    qCoeff g (p * n) + ε (p : ZMod M) * (p : ℂ) ^ (k - 1) * (if p ∣ n then qCoeff g (n / p) else 0) =
      c * qCoeff g n := by
  have hcop : Nat.Coprime p M := (Nat.Prime.coprime_iff_not_dvd hp).2 hpM
  obtain ⟨σ, hσ⟩ := CuspForm.exists_isDiamondLift_of_coprime hcop
  have hdiam : CuspForm.diamondLinOne M k p g = ε (p : ZMod M) • g := hε.diamondLinOne_apply_eq_smul hcop
  have hslashσ : (⇑g) ∣[k] (Matrix.SpecialLinearGroup.mapGL ℝ σ : GL (Fin 2) ℝ) = ε (p : ZMod M) • ⇑g := by
    rw [← CuspForm.coe_diamondLinOne_apply hσ g, hdiam]; rfl
  have hT1 : CuspForm.heckeTLinOne k hp hpM g = c • g := by
    apply DFunLike.coe_fn_eq.mp
    rw [CuspForm.coe_heckeTLinOne_apply_of_isDiamondLift k hp hpM hσ g, hslashσ,
      ModularForm.smul_slash, ModularForm.σ_heckeDiagMatrix]
    simpa using hTp
  have hq := CuspForm.qCoeff_heckeTLinOne k hp hpM g n
  rw [hT1, hdiam, qCoeff_smul] at hq
  have hq' : c * qCoeff (⇑g) n = qCoeff (⇑g) (p * n) +
      (p : ℂ) ^ (k - 1) * (if p ∣ n then ε (p : ZMod M) * qCoeff (⇑g) (n / p) else 0) := by
    rw [hq]; split_ifs <;> simp [qCoeff_smul']
  rw [hq']
  split_ifs <;> ring

theorem qrel_U (g : CuspForm (Gamma1 M) k) {q : ℕ} (hq : q ≠ 0) (c : ℂ)
    (hUq : ModularForm.heckeU k q ⇑g = c • ⇑g) (n : ℕ) :
    qCoeff g (q * n) = c * qCoeff g n := by
  have h := ModularFormClass.qCoeff_heckeU g one_mem_strictPeriods_Gamma1 hq n
  rw [hUq, ModularForm.coeffHeckeU_apply, ← CuspForm.IsGLPos.coe_smul, qCoeff_smul,
    mul_comm n q] at h
  exact h.symm

end GammaOne

end Ws41.FormsU

open Ws41.FormsU in
theorem solution
    (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) (k : ℤ) (S : Set ℕ) (Q : Set ℕ)
    (hQ : ∀ q ∈ Q, q ∣ M) (a b : ℕ → ℂ) (e : (ZMod M)ˣ →* ℂˣ)
    (f : CuspForm (CohCarrier.GammaH M H) k) (hf : f ≠ 0)
    (hT : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime), ℓ ∉ S → ∀ (hℓM : ¬ ℓ ∣ M),
      CuspForm.heckeTLinH k hℓ hℓM f = a ℓ • f)
    (hU : ∀ q ∈ Q, CuspForm.heckeULinH k q f = b q • f)
    (hD : ∀ u : (ZMod M)ˣ, CuspForm.diamondLinH k u f = (e u : ℂ) • f) :
    ∃ (ε : DirichletCharacter ℂ M) (h : CuspForm (CongruenceSubgroup.Gamma1 M) k),
      CuspForm.IsEigenformWith ε h ∧
      (∀ u : (ZMod M)ˣ, ε (u : ZMod M) = e u) ∧
      (∀ ℓ : ℕ, ℓ.Prime → ℓ ∉ S → ¬ ℓ ∣ M → ModularFormClass.qCoeff h ℓ = a ℓ) ∧
      (∀ q ∈ Q, ModularFormClass.qCoeff h q = b q) := by
  classical
  haveI : FiniteDimensional ℂ (CuspForm (CohCarrier.GammaH M H) k) := finiteDimensional_gammaH

  set X : Submodule ℂ (CuspForm (CohCarrier.GammaH M H) k) := jointEig k S Q a b e with hXdef
  have hfX : f ∈ X := mem_jointEig_iff.2 ⟨hT, hU, hD⟩
  haveI : Nontrivial X := nontrivial_of_ne (⟨f, hfX⟩ : X) 0 fun h => hf (congrArg Subtype.val h)
  let T : Idx M → Module.End ℂ X := fun i => (op k i).restrict fun x hx => op_mem_jointEig hQ i hx
  have hcomm : ∀ i j, Commute (T i) (T j) := fun i j =>
    LinearMap.ext fun x => Subtype.ext (op_comm i j (x : CuspForm (CohCarrier.GammaH M H) k))
  obtain ⟨χ, v, hv0, hv⟩ := Module.End.exists_common_eigenvector_of_commute T hcomm
  set f₀ : CuspForm (CohCarrier.GammaH M H) k := (v : CuspForm (CohCarrier.GammaH M H) k) with hf₀def
  have hf₀0 : f₀ ≠ 0 := fun h => hv0 (Subtype.ext h)
  have hEig : ∀ i, op k i f₀ = χ i • f₀ := fun i => congrArg Subtype.val (hv i)
  obtain ⟨hT₀, hU₀, hD₀⟩ := mem_jointEig_iff.1 v.2

  let B : ℕ → ℂ := fun p =>
    if hp : p.Prime then (if hpM : p ∣ M then χ (Sum.inr (Sum.inl ⟨p, hp, hpM⟩)) else χ (Sum.inl ⟨p, hp, hpM⟩))
    else 0
  have hBT : ∀ (p : ℕ) (hp : p.Prime) (hpM : ¬ p ∣ M), CuspForm.heckeTLinH k hp hpM f₀ = B p • f₀ := by
    intro p hp hpM
    have := hEig (Sum.inl ⟨p, hp, hpM⟩)
    simp only [B, dif_pos hp, dif_neg hpM]
    exact this
  have hBU : ∀ p : ℕ, p.Prime → p ∣ M → CuspForm.heckeULinH k p f₀ = B p • f₀ := by
    intro p hp hpM
    have := hEig (Sum.inr (Sum.inl ⟨p, hp, hpM⟩))
    simp only [B, dif_pos hp, dif_pos hpM]
    exact this

  obtain ⟨g, hg⟩ := CuspForm.exists_gamma1_coe_eq_of_gammaH M H k f₀
  have hg0 : g ≠ 0 := by
    intro h
    apply hf₀0
    apply DFunLike.coe_fn_eq.mp
    rw [← hg, h]
    rfl
  set ε : DirichletCharacter ℂ M := MulChar.ofUnitHom e with hεdef
  have hεe : ∀ u : (ZMod M)ˣ, ε (u : ZMod M) = e u := fun u => MulChar.ofUnitHom_coe e u
  have hNeb : CuspForm.HasNebentypus ε g := hasNebentypus_of_diamond e f₀ hD₀ g hg
  obtain ⟨-, hcT, hcU⟩ :=
    CuspForm.coe_diamondLinH_and_coe_heckeTLinH_and_coe_heckeULinH_of_hasNebentypus M H k ε f₀ g hg.symm hNeb

  have hrelT : ∀ p : ℕ, p.Prime → ¬ p ∣ M → ∀ n : ℕ,
      ModularFormClass.qCoeff g (p * n) +
          ε (p : ZMod M) * (p : ℂ) ^ (k - 1) *
            (if p ∣ n then ModularFormClass.qCoeff g (n / p) else 0) =
        B p * ModularFormClass.qCoeff g n := by
    intro p hp hpM n
    refine qrel_T g ε hNeb hp hpM (B p) ?_ n
    rw [← hcT p hp hpM, hBT p hp hpM, CuspForm.IsGLPos.coe_smul, hg]
  have hrelU : ∀ q : ℕ, q.Prime → q ∣ M → ∀ n : ℕ,
      ModularFormClass.qCoeff g (q * n) = B q * ModularFormClass.qCoeff g n := by
    intro q hq hqM n
    refine qrel_U g hq.ne_zero (B q) ?_ n
    rw [← hcU q hq hqM, hBU q hq hqM, CuspForm.IsGLPos.coe_smul, hg]

  obtain ⟨h1ne, hEigen, hcoef⟩ :=
    CuspForm.qCoeff_one_ne_zero_and_isEigenformWith_smul_of_hasNebentypus_of_qCoeff_hecke_eigen_forall
      M k ε g hg0 hNeb B hrelT hrelU
  set h : CuspForm (CongruenceSubgroup.Gamma1 M) k := (ModularFormClass.qCoeff g 1)⁻¹ • g with hhdef
  have hcoef' : ∀ p : ℕ, p.Prime → ModularFormClass.qCoeff (⇑h) p = B p := fun p hp => by
    rw [hhdef, CuspForm.IsGLPos.coe_smul]; exact hcoef p hp

  have key : ∀ q : ℕ, q ∣ M → CuspForm.heckeULinH k q f₀ = ModularFormClass.qCoeff h q • f₀ := by
    intro q
    induction q using Nat.strong_induction_on with
    | _ q ih =>
      intro hqM
      have hq0 : q ≠ 0 := fun h0 => (NeZero.ne M) (Nat.eq_zero_of_zero_dvd (h0 ▸ hqM))
      by_cases hq1 : q = 1
      · subst hq1
        rw [heckeULinH_one, hEigen.qCoeff_one, one_smul]
      · have hp : q.minFac.Prime := Nat.minFac_prime hq1
        obtain ⟨m, hm⟩ := (Nat.minFac_dvd q : q.minFac ∣ q)
        have hm0 : m ≠ 0 := by rintro rfl; exact hq0 (by rw [hm, mul_zero])
        have hmlt : m < q := by
          rw [hm]; exact lt_mul_of_one_lt_left (Nat.pos_of_ne_zero hm0) hp.one_lt
        have hqM' : q.minFac * m ∣ M := hm ▸ hqM
        have hmM : m ∣ M := Nat.dvd_trans (Dvd.intro_left _ rfl) hqM'
        have hpM : q.minFac ∣ M := Nat.dvd_trans (Dvd.intro m rfl) hqM'
        rw [hm, heckeULinH_mul hqM', ih m hmlt hmM, map_smul, hBU _ hp hpM, ← hcoef' _ hp,
          hEigen.hecke_of_dvd hp hpM m, smul_smul, mul_comm]
  refine ⟨ε, h, hEigen, hεe, ?_, ?_⟩
  · intro ℓ hℓ hℓS hℓM
    rw [hcoef' ℓ hℓ]
    have e1 := hT₀ ℓ hℓ hℓS hℓM
    rw [hBT ℓ hℓ hℓM] at e1
    exact smul_left_injective ℂ hf₀0 e1
  · intro q hq
    have e1 := hU₀ q hq
    rw [key q (hQ q hq)] at e1
    exact smul_left_injective ℂ hf₀0 e1

end
end S_CuspForm_exists_isEigenformWith_qCoeff_eq_of_heckeTLinH_eq_smul_of_heckeULinH_eq_smul_of_diamondLinH_eq_smul
end P2MW
export P2MW.S_CuspForm_exists_isEigenformWith_qCoeff_eq_of_heckeTLinH_eq_smul_of_heckeULinH_eq_smul_of_diamondLinH_eq_smul (solution)
