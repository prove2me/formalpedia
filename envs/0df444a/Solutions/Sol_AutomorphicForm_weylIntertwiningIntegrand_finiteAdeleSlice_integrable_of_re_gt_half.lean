-- Prove2me | solution 1 for AutomorphicForm.weylIntertwiningIntegrand_finiteAdeleSlice_integrable_of_re_gt_half
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/5479bbca-c3e8-52a6-a394-b9bc0cbe13d2

import Definitions.Def_AutomorphicForm_InducedSection
import Definitions.Def_AutomorphicForm_EtaFamily
import Definitions.Def_AutomorphicForm_WeylIntertwining
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_NumberField_AdelicBox
import Theorems.Thm_NumberField_tsum_prod_absNorm_heightOneSpectrum_pow_rpow_neg_lt_top
import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_weylIntertwiningIntegrand_finiteAdeleSlice_integrable_of_re_gt_half

set_option autoImplicit false

noncomputable section

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicBox IsDedekindDomain
open scoped ENNReal NNReal Pointwise

namespace AutomorphicForm
p2m_export "AutomorphicForm" "IsInducedSection borelSubgroup borelDiagFst borelDiagSnd globalPoints_apply AdelicGL2 IsUnitaryChar unipotentGL2 unipotentGL2_coe unipotentGL2_zero unipotentGL2_add norm_cpowChar_apply etaFst etaSnd etaFst_apply etaSnd_apply gl2Weyl gl2Weyl_inv adelicWeyl"
namespace WeylIntegrable
p2m_open "AutomorphicForm"

section Coset

variable (F : Type) [Field F] [NumberField F]

local notation "𝔸" => AdeleRing (𝓞 F) F
local notation "𝔸∞" => InfiniteAdeleRing F
local notation "𝔸f" => FiniteAdeleRing (𝓞 F) F

attribute [local instance] NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel

def toAdele (a : 𝔸∞) (b : 𝔸f) : 𝔸 := (a, b)

@[scoped simp] theorem toAdele_fst (a : 𝔸∞) (b : 𝔸f) : (toAdele F a b).1 = a := rfl
@[scoped simp] theorem toAdele_snd (a : 𝔸∞) (b : 𝔸f) : (toAdele F a b).2 = b := rfl

def slab (S : Set 𝔸∞) (T : Set 𝔸f) : Set 𝔸 := {x | x.1 ∈ S ∧ x.2 ∈ T}

theorem mem_slab {S : Set 𝔸∞} {T : Set 𝔸f} {x : 𝔸} : x ∈ slab F S T ↔ x.1 ∈ S ∧ x.2 ∈ T := Iff.rfl

theorem isClosed_slab {S : Set 𝔸∞} {T : Set 𝔸f} (hS : IsClosed S) (hT : IsClosed T) : IsClosed (slab F S T) :=
  (hS.preimage continuous_fst).inter (hT.preimage continuous_snd)

theorem vadd_slab (S : Set 𝔸∞) (T : Set 𝔸f) (c : 𝔸f) :
    toAdele F 0 c +ᵥ slab F S T = slab F S (c +ᵥ T) := by
  ext x
  simp only [Set.mem_vadd_set, mem_slab, vadd_eq_add]
  constructor
  · rintro ⟨z, ⟨hz1, hz2⟩, rfl⟩
    have h1 : (toAdele F 0 c + z).1 = z.1 := show (0 : 𝔸∞) + z.1 = z.1 from zero_add _
    have h2 : (toAdele F 0 c + z).2 = c + z.2 := rfl
    rw [h1, h2]
    exact ⟨hz1, z.2, hz2, rfl⟩
  · rintro ⟨hx1, ⟨t, ht, hxt⟩⟩
    refine ⟨toAdele F x.1 t, ⟨hx1, ht⟩, Prod.ext ?_ ?_⟩
    · show (0 : 𝔸∞) + x.1 = x.1
      rw [zero_add]
    · show c + t = x.2
      exact hxt

theorem measure_slab_eq_relIndex_mul (μ : Measure 𝔸) [μ.IsAddLeftInvariant] {S : Set 𝔸∞} (hS : IsClosed S)
    (A B : AddSubgroup 𝔸f) (hAB : A ≤ B) (hA : IsClosed (A : Set 𝔸f)) (hfin : A.relIndex B ≠ 0) :
    μ (slab F S B) = A.relIndex B * μ (slab F S A) := by
  classical

  set H : AddSubgroup B := A.addSubgroupOf B with hH
  haveI : H.FiniteIndex := ⟨hfin⟩
  obtain ⟨s, hs, -⟩ := H.exists_isComplement_left 0
  haveI : Finite s := hs.finite_left_iff.mpr inferInstance
  have hcard : Nat.card s = A.relIndex B := hs.card_left

  have hcover : (B : Set 𝔸f) = ⋃ c : s, ((c : B) : 𝔸f) +ᵥ (A : Set 𝔸f) := by
    ext b
    simp only [Set.mem_iUnion, Set.mem_vadd_set, SetLike.mem_coe]
    constructor
    · intro hb
      have hmem : (⟨b, hb⟩ : B) ∈ (Set.univ : Set B) := Set.mem_univ _
      rw [← hs.add_eq] at hmem
      obtain ⟨c, hc, h, hh, hsum⟩ := Set.mem_add.mp hmem
      refine ⟨⟨c, hc⟩, (h : 𝔸f), ?_, ?_⟩
      · exact AddSubgroup.mem_addSubgroupOf.mp hh
      · exact congrArg Subtype.val hsum
    · rintro ⟨c, a, ha, rfl⟩
      exact B.add_mem (c : B).2 (hAB ha)
  have hdisj : Pairwise fun c c' : s => Disjoint (((c : B) : 𝔸f) +ᵥ (A : Set 𝔸f)) (((c' : B) : 𝔸f) +ᵥ (A : Set 𝔸f)) := by
    intro c c' hcc'
    have hd : Disjoint ((c : B) +ᵥ (H : Set B)) ((c' : B) +ᵥ (H : Set B)) :=
      hs.pairwiseDisjoint_vadd c.2 c'.2 (fun h => hcc' (Subtype.ext h))
    rw [Set.disjoint_iff_forall_ne]
    rintro _ ⟨a, ha, rfl⟩ _ ⟨a', ha', rfl⟩ heq
    have haB : a ∈ B := hAB ha
    have ha'B : a' ∈ B := hAB ha'
    refine hd.ne_of_mem (Set.mem_vadd_set.mpr ⟨⟨a, haB⟩, AddSubgroup.mem_addSubgroupOf.mpr ha, rfl⟩)
      (Set.mem_vadd_set.mpr ⟨⟨a', ha'B⟩, AddSubgroup.mem_addSubgroupOf.mpr ha', rfl⟩) ?_
    exact Subtype.ext heq

  have hslab : slab F S B = ⋃ c : s, slab F S (((c : B) : 𝔸f) +ᵥ (A : Set 𝔸f)) := by
    ext x; simp only [mem_slab, hcover, Set.mem_iUnion]; exact ⟨fun ⟨h1, c, h2⟩ => ⟨c, h1, h2⟩, fun ⟨c, h1, h2⟩ => ⟨h1, c, h2⟩⟩
  have hmeasA : MeasurableSet (slab F S (A : Set 𝔸f)) := (isClosed_slab F hS hA).measurableSet
  have hmeas : ∀ c : s, MeasurableSet (slab F S (((c : B) : 𝔸f) +ᵥ (A : Set 𝔸f))) := fun c => by
    rw [← vadd_slab]; exact hmeasA.const_vadd _
  have hdisj' : Pairwise fun c c' : s => Disjoint (slab F S (((c : B) : 𝔸f) +ᵥ (A : Set 𝔸f))) (slab F S (((c' : B) : 𝔸f) +ᵥ (A : Set 𝔸f))) := by
    intro c c' hcc'
    rw [Set.disjoint_iff_forall_ne]
    rintro x ⟨-, hx⟩ x' ⟨-, hx'⟩ rfl
    exact Set.disjoint_iff_forall_ne.mp (hdisj hcc') hx hx' rfl
  have hconst : ∀ c : s, μ (slab F S (((c : B) : 𝔸f) +ᵥ (A : Set 𝔸f))) = μ (slab F S A) := fun c => by
    rw [← vadd_slab, measure_vadd]
  rw [hslab, measure_iUnion hdisj' hmeas, tsum_congr hconst]
  haveI := Fintype.ofFinite s
  rw [tsum_fintype, Finset.sum_const, Finset.card_univ, ← Nat.card_eq_fintype_card, hcard, nsmul_eq_mul]

end Coset

section ModFin

variable (F : Type) [Field F] [NumberField F]

local notation "𝔸" => AdeleRing (𝓞 F) F
local notation "𝔸∞" => InfiniteAdeleRing F
local notation "𝔸f" => FiniteAdeleRing (𝓞 F) F

attribute [local instance] NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel
  NumberField.AdelicHaar.isAddHaarMeasure_adelicAddHaar

def intLattice : AddSubgroup 𝔸f where
  carrier := integralFiniteAdeles (𝓞 F) F
  zero_mem' := fun _ => zero_mem _
  add_mem' hx hy := fun v => add_mem (hx v) (hy v)
  neg_mem' hx := fun v => neg_mem (hx v)

@[scoped simp] theorem coe_intLattice : (intLattice F : Set 𝔸f) = integralFiniteAdeles (𝓞 F) F := rfl

def dilate (y : (𝔸f)ˣ) : AddSubgroup 𝔸f := (intLattice F).map (DistribSMul.toAddMonoidHom 𝔸f (y : 𝔸f))

theorem coe_dilate (y : (𝔸f)ˣ) : (dilate F y : Set 𝔸f) = (y : 𝔸f) • integralFiniteAdeles (𝓞 F) F := by
  ext z; simp [dilate, Set.mem_smul_set]

def finIdele (y : (𝔸f)ˣ) : (𝔸)ˣ where
  val := toAdele F 1 (y : 𝔸f)
  inv := toAdele F 1 ((y⁻¹ : (𝔸f)ˣ) : 𝔸f)
  val_inv := Prod.ext (show (1 : 𝔸∞) * 1 = 1 from one_mul 1) (show (y : 𝔸f) * ((y⁻¹ : (𝔸f)ˣ) : 𝔸f) = 1 from Units.mul_inv y)
  inv_val := Prod.ext (show (1 : 𝔸∞) * 1 = 1 from one_mul 1) (show ((y⁻¹ : (𝔸f)ˣ) : 𝔸f) * (y : 𝔸f) = 1 from Units.inv_mul y)

theorem finIdele_smul_slab (y : (𝔸f)ˣ) (S : Set 𝔸∞) (T : Set 𝔸f) :
    finIdele F y • slab F S T = slab F S ((y : 𝔸f) • T) := by
  ext x
  simp only [Set.mem_smul_set, mem_slab]
  constructor
  · rintro ⟨z, ⟨hz1, hz2⟩, rfl⟩
    have h1 : (finIdele F y • z).1 = z.1 := show (1 : 𝔸∞) * z.1 = z.1 from one_mul _
    have h2 : (finIdele F y • z).2 = (y : 𝔸f) * z.2 := rfl
    rw [h1, h2]
    exact ⟨hz1, z.2, hz2, rfl⟩
  · rintro ⟨hx1, ⟨t, ht, hxt⟩⟩
    refine ⟨toAdele F x.1 t, ⟨hx1, ht⟩, Prod.ext ?_ ?_⟩
    · show (1 : 𝔸∞) * x.1 = x.1
      rw [one_mul]
    · show (y : 𝔸f) * t = x.2
      exact hxt

theorem distribHaarChar_finIdele (y : (𝔸f)ˣ) (hy : intLattice F ≤ dilate F y) (hfin : (intLattice F).relIndex (dilate F y) ≠ 0) :
    (distribHaarChar 𝔸 (finIdele F y) : ℝ≥0∞) = (intLattice F).relIndex (dilate F y) := by

  obtain ⟨S, hScpt, hSnhds⟩ := exists_compact_mem_nhds (0 : 𝔸∞)
  have hSclosed : IsClosed S := hScpt.isClosed
  have hZclosed : IsClosed (integralFiniteAdeles (𝓞 F) F) := isClosed_integralFiniteAdeles F
  have hZopen : IsOpen (integralFiniteAdeles (𝓞 F) F) := isOpen_integralFiniteAdeles F
  have hZcpt : IsCompact (integralFiniteAdeles (𝓞 F) F) := isCompact_integralFiniteAdeles F
  set μ : Measure 𝔸 := adelicAddHaar (𝓞 F) F
  have hpos : 0 < μ (slab F S (integralFiniteAdeles (𝓞 F) F)) := by
    have hU : IsOpen (slab F (interior S) (integralFiniteAdeles (𝓞 F) F)) :=
      (isOpen_interior.preimage continuous_fst).inter (hZopen.preimage continuous_snd)
    have hne : (slab F (interior S) (integralFiniteAdeles (𝓞 F) F)).Nonempty :=
      ⟨((0 : 𝔸∞), (0 : 𝔸f)), mem_interior_iff_mem_nhds.mpr hSnhds, (intLattice F).zero_mem⟩
    exact (hU.measure_pos μ hne).trans_le (measure_mono fun x ⟨h1, h2⟩ => ⟨interior_subset h1, h2⟩)
  have hlt : μ (slab F S (integralFiniteAdeles (𝓞 F) F)) < ∞ := by
    have hc : IsCompact (slab F S (integralFiniteAdeles (𝓞 F) F)) := by
      have : slab F S (integralFiniteAdeles (𝓞 F) F) = (fun p : 𝔸∞ × 𝔸f => (p : 𝔸)) '' (S ×ˢ integralFiniteAdeles (𝓞 F) F) := by
        ext x; simp only [mem_slab]
        exact ⟨fun ⟨h1, h2⟩ => ⟨(x.1, x.2), ⟨h1, h2⟩, rfl⟩, by rintro ⟨p, ⟨h1, h2⟩, rfl⟩; exact ⟨h1, h2⟩⟩
      rw [this]
      exact (hScpt.prod hZcpt).image continuous_id
    exact hc.measure_lt_top

  haveI : μ.Regular := by
    show (adelicAddHaar (𝓞 F) F).Regular
    unfold adelicAddHaar
    infer_instance
  have h := distribHaarChar_mul μ (finIdele F y) (slab F S (integralFiniteAdeles (𝓞 F) F))
  rw [finIdele_smul_slab, ← coe_dilate, ← coe_intLattice,
    measure_slab_eq_relIndex_mul F μ hSclosed (intLattice F) (dilate F y) hy hZclosed hfin] at h
  exact (ENNReal.mul_left_inj hpos.ne' hlt.ne).mp h

end ModFin

end AutomorphicForm.WeylIntegrable
p2m_reactivate "P2MW.S_AutomorphicForm_weylIntertwiningIntegrand_finiteAdeleSlice_integrable_of_re_gt_half.AutomorphicForm P2MW.S_AutomorphicForm_weylIntertwiningIntegrand_finiteAdeleSlice_integrable_of_re_gt_half.AutomorphicForm.WeylIntegrable"
p2m_reactivate "P2MW.S_AutomorphicForm_weylIntertwiningIntegrand_finiteAdeleSlice_integrable_of_re_gt_half.AutomorphicForm"

end
p2m_reactivate "P2MW.S_AutomorphicForm_weylIntertwiningIntegrand_finiteAdeleSlice_integrable_of_re_gt_half.AutomorphicForm P2MW.S_AutomorphicForm_weylIntertwiningIntegrand_finiteAdeleSlice_integrable_of_re_gt_half.AutomorphicForm.WeylIntegrable"

noncomputable section

open NumberField IsDedekindDomain
open scoped Classical

namespace AutomorphicForm
p2m_export "AutomorphicForm" "IsInducedSection borelSubgroup borelDiagFst borelDiagSnd globalPoints_apply AdelicGL2 IsUnitaryChar unipotentGL2 unipotentGL2_coe unipotentGL2_zero unipotentGL2_add norm_cpowChar_apply etaFst etaSnd etaFst_apply etaSnd_apply gl2Weyl gl2Weyl_inv adelicWeyl"
namespace WeylIntegrable
p2m_open "AutomorphicForm"

section Generic

variable {A : Type*} [CommRing A] {ε y z x : A}

structure SelRel (ε y z x : A) : Prop where
  idem : ε * ε = ε
  yz : y * z = 1
  small : (1 - ε) * y = 1 - ε
  big : ε * y = ε * x

def bMat (ε y z : A) : Matrix (Fin 2) (Fin 2) A := !![1 - ε - ε * z, ε; 0, y]

def mMat (ε z x : A) : Matrix (Fin 2) (Fin 2) A := !![ε, 1 - ε; 1 - ε + ε * z, (1 - ε) * x + ε]

def mInvMat (ε z x : A) : Matrix (Fin 2) (Fin 2) A :=
  !![(2 * ε - 1) * ((1 - ε) * x + ε), -((2 * ε - 1) * (1 - ε)); -((2 * ε - 1) * (1 - ε + ε * z)), (2 * ε - 1) * ε]

theorem det_bMat (h : SelRel ε y z x) : (bMat ε y z).det = 1 - 2 * ε := by
  rw [bMat, Matrix.det_fin_two_of]
  linear_combination h.small - ε * h.yz

theorem one_sub_two_mul_sq (h : SelRel ε y z x) : (1 - 2 * ε) * (1 - 2 * ε) = 1 := by
  linear_combination 4 * h.idem

theorem isUnit_det_bMat (h : SelRel ε y z x) : IsUnit (bMat ε y z).det := by
  rw [det_bMat h]; exact (Units.mkOfMulEqOne _ _ (one_sub_two_mul_sq h)).isUnit

def bFactor (h : SelRel ε y z x) : GL (Fin 2) A := Matrix.nonsingInvUnit (bMat ε y z) (isUnit_det_bMat h)

@[scoped simp] theorem coe_bFactor (h : SelRel ε y z x) : (bFactor h : Matrix (Fin 2) (Fin 2) A) = bMat ε y z := rfl

theorem bFactor_mem_borel (h : SelRel ε y z x) : bFactor h ∈ borelSubgroup A := by
  show (bFactor h : Matrix (Fin 2) (Fin 2) A) 1 0 = 0
  simp [bMat]

theorem borelDiagFst_bFactor_val (h : SelRel ε y z x) :
    ((borelDiagFst ⟨bFactor h, bFactor_mem_borel h⟩ : Aˣ) : A) = 1 - ε - ε * z := by
  show (bFactor h : Matrix (Fin 2) (Fin 2) A) 0 0 = _
  simp [bMat]

theorem borelDiagSnd_bFactor_val (h : SelRel ε y z x) :
    ((borelDiagSnd ⟨bFactor h, bFactor_mem_borel h⟩ : Aˣ) : A) = y := by
  show (bFactor h : Matrix (Fin 2) (Fin 2) A) 1 1 = _
  simp [bMat]

theorem bMat_mul_mMat (h : SelRel ε y z x) : bMat ε y z * mMat ε z x = !![0, 1; 1, x] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [bMat, mMat, Matrix.mul_apply, Fin.sum_univ_two]
  · linear_combination (-2) * h.idem
  · linear_combination (2 + z - x) * h.idem
  · linear_combination h.small + ε * h.yz
  · linear_combination x * h.small + h.big

end Generic
p2m_reactivate "P2MW.S_AutomorphicForm_weylIntertwiningIntegrand_finiteAdeleSlice_integrable_of_re_gt_half.AutomorphicForm P2MW.S_AutomorphicForm_weylIntertwiningIntegrand_finiteAdeleSlice_integrable_of_re_gt_half.AutomorphicForm.WeylIntegrable"

section Adelic

variable (F : Type) [Field F] [NumberField F]

local notation "𝔸" => AdeleRing (𝓞 F) F
local notation "𝔸∞" => InfiniteAdeleRing F
local notation "𝔸f" => FiniteAdeleRing (𝓞 F) F

def toAdele' (a : 𝔸∞) (b : 𝔸f) : 𝔸 := (a, b)

def finOfIntegral (f : (v : HeightOneSpectrum (𝓞 F)) → v.adicCompletion F)
    (hf : ∀ v, f v ∈ v.adicCompletionIntegers F) : 𝔸f :=
  show RestrictedProduct (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
      (fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F))) Filter.cofinite from
    RestrictedProduct.mk f (.of_forall hf)

@[scoped simp] theorem finOfIntegral_apply (f : (v : HeightOneSpectrum (𝓞 F)) → v.adicCompletion F)
    (hf : ∀ v, f v ∈ v.adicCompletionIntegers F) (v : HeightOneSpectrum (𝓞 F)) : finOfIntegral F f hf v = f v := rfl

def BigInf (a : 𝔸∞) (w : InfinitePlace F) : Prop := 1 < ‖a w‖

def BigFin (b : 𝔸f) (v : HeightOneSpectrum (𝓞 F)) : Prop := b v ∉ v.adicCompletionIntegers F

omit [NumberField F] in
theorem ne_zero_of_bigInf {a : 𝔸∞} {w : InfinitePlace F} (h : BigInf F a w) : a w ≠ 0 := by
  intro h0; rw [BigInf, h0, norm_zero] at h; exact (not_lt.mpr zero_le_one) h

omit [NumberField F] in
theorem norm_inv_lt_one_of_bigInf {a : 𝔸∞} {w : InfinitePlace F} (h : BigInf F a w) : ‖(a w)⁻¹‖ < 1 := by
  rw [norm_inv]; exact inv_lt_one_of_one_lt₀ h

theorem one_lt_valued_of_bigFin {b : 𝔸f} {v : HeightOneSpectrum (𝓞 F)} (h : BigFin F b v) : 1 < Valued.v (b v) := by
  rw [BigFin, HeightOneSpectrum.mem_adicCompletionIntegers, not_le] at h; exact h

theorem ne_zero_of_bigFin {b : 𝔸f} {v : HeightOneSpectrum (𝓞 F)} (h : BigFin F b v) : b v ≠ 0 := by
  intro h0; have := one_lt_valued_of_bigFin F h; rw [h0, map_zero] at this; exact (not_lt.mpr zero_le_one) this

theorem inv_mem_of_bigFin {b : 𝔸f} {v : HeightOneSpectrum (𝓞 F)} (h : BigFin F b v) : (b v)⁻¹ ∈ v.adicCompletionIntegers F := by
  rw [HeightOneSpectrum.mem_adicCompletionIntegers]
  exact ((Valuation.one_lt_val_iff _ (ne_zero_of_bigFin F h)).mp (one_lt_valued_of_bigFin F h)).le

def selE (a : 𝔸∞) (b : 𝔸f) : 𝔸 := toAdele' F (fun w => if BigInf F a w then 1 else 0)
  (finOfIntegral F (fun v => if BigFin F b v then 1 else 0) fun v => by split_ifs <;> simp [one_mem, zero_mem])

def selZ (a : 𝔸∞) (b : 𝔸f) : 𝔸 := toAdele' F (fun w => if BigInf F a w then (a w)⁻¹ else 1)
  (finOfIntegral F (fun v => if BigFin F b v then (b v)⁻¹ else 1) fun v => by
    split_ifs with h
    · exact inv_mem_of_bigFin F h
    · exact one_mem _)

end Adelic
p2m_reactivate "P2MW.S_AutomorphicForm_weylIntertwiningIntegrand_finiteAdeleSlice_integrable_of_re_gt_half.AutomorphicForm P2MW.S_AutomorphicForm_weylIntertwiningIntegrand_finiteAdeleSlice_integrable_of_re_gt_half.AutomorphicForm.WeylIntegrable"

section Generic2

variable {A : Type*} [CommRing A] {ε y z x : A}

def yUnit (h : SelRel ε y z x) : Aˣ :=
  ⟨y, ε * z + (1 - ε), by linear_combination ε * h.yz + h.small, by linear_combination ε * h.yz + h.small⟩

@[scoped simp] theorem coe_yUnit (h : SelRel ε y z x) : (yUnit h : A) = y := rfl
theorem coe_yUnit_inv (h : SelRel ε y z x) : (((yUnit h)⁻¹ : Aˣ) : A) = ε * z + (1 - ε) := rfl

def eUnit (h : SelRel ε y z x) : Aˣ := ⟨1 - 2 * ε, 1 - 2 * ε, one_sub_two_mul_sq h, one_sub_two_mul_sq h⟩

@[scoped simp] theorem coe_eUnit (h : SelRel ε y z x) : (eUnit h : A) = 1 - 2 * ε := rfl

theorem eUnit_mul_self (h : SelRel ε y z x) : eUnit h * eUnit h = 1 := Units.ext (one_sub_two_mul_sq h)

theorem borelDiagFst_bFactor (h : SelRel ε y z x) : borelDiagFst ⟨bFactor h, bFactor_mem_borel h⟩ = eUnit h * (yUnit h)⁻¹ := by
  apply Units.ext
  rw [borelDiagFst_bFactor_val, Units.val_mul, coe_eUnit, coe_yUnit_inv]
  linear_combination (2 * z - 2) * h.idem

theorem borelDiagSnd_bFactor (h : SelRel ε y z x) : borelDiagSnd ⟨bFactor h, bFactor_mem_borel h⟩ = yUnit h :=
  Units.ext (borelDiagSnd_bFactor_val h)

theorem mMat_mul_mInvMat (h : SelRel ε y z x) : mMat ε z x * mInvMat ε z x = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [mMat, mInvMat, Matrix.mul_apply, Fin.sum_univ_two]
  · linear_combination (4 - (2 * ε - 1) * x + (2 * ε - 1) * z) * h.idem
  · ring
  · ring
  · linear_combination (4 + (2 * ε - 1) * z - (2 * ε - 1) * x) * h.idem

end Generic2
p2m_reactivate "P2MW.S_AutomorphicForm_weylIntertwiningIntegrand_finiteAdeleSlice_integrable_of_re_gt_half.AutomorphicForm P2MW.S_AutomorphicForm_weylIntertwiningIntegrand_finiteAdeleSlice_integrable_of_re_gt_half.AutomorphicForm.WeylIntegrable"

section Adelic2

variable (F : Type) [Field F] [NumberField F]

local notation "𝔸" => AdeleRing (𝓞 F) F
local notation "𝔸∞" => InfiniteAdeleRing F
local notation "𝔸f" => FiniteAdeleRing (𝓞 F) F

def selY (a : 𝔸∞) (b : 𝔸f) : 𝔸 := toAdele' F (fun w => if BigInf F a w then a w else 1)
  (show RestrictedProduct (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
      (fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F))) Filter.cofinite from
    RestrictedProduct.mk (fun v => if BigFin F b v then b v else 1)
      ((show RestrictedProduct (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
          (fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F))) Filter.cofinite from b).eventually.mono
        fun v hv => by
          rw [if_neg (show ¬ BigFin F b v from not_not.mpr hv)]
          exact one_mem _))

theorem selE_fst (a : 𝔸∞) (b : 𝔸f) (w : InfinitePlace F) : (selE F a b).1 w = if BigInf F a w then 1 else 0 := rfl
theorem selE_snd (a : 𝔸∞) (b : 𝔸f) (v : HeightOneSpectrum (𝓞 F)) : (selE F a b).2 v = if BigFin F b v then 1 else 0 := rfl
theorem selY_fst (a : 𝔸∞) (b : 𝔸f) (w : InfinitePlace F) : (selY F a b).1 w = if BigInf F a w then a w else 1 := rfl
theorem selY_snd (a : 𝔸∞) (b : 𝔸f) (v : HeightOneSpectrum (𝓞 F)) : (selY F a b).2 v = if BigFin F b v then b v else 1 := rfl
theorem selZ_fst (a : 𝔸∞) (b : 𝔸f) (w : InfinitePlace F) : (selZ F a b).1 w = if BigInf F a w then (a w)⁻¹ else 1 := rfl
theorem selZ_snd (a : 𝔸∞) (b : 𝔸f) (v : HeightOneSpectrum (𝓞 F)) : (selZ F a b).2 v = if BigFin F b v then (b v)⁻¹ else 1 := rfl
theorem toAdele'_fst (a : 𝔸∞) (b : 𝔸f) : (toAdele' F a b).1 = a := rfl
theorem toAdele'_snd (a : 𝔸∞) (b : 𝔸f) : (toAdele' F a b).2 = b := rfl

theorem mul_fst_apply (u u' : 𝔸) (w : InfinitePlace F) : (u * u').1 w = u.1 w * u'.1 w := rfl
theorem mul_snd_apply (u u' : 𝔸) (v : HeightOneSpectrum (𝓞 F)) : (u * u').2 v = u.2 v * u'.2 v := rfl
theorem sub_fst_apply (u u' : 𝔸) (w : InfinitePlace F) : (u - u').1 w = u.1 w - u'.1 w := rfl
theorem sub_snd_apply (u u' : 𝔸) (v : HeightOneSpectrum (𝓞 F)) : (u - u').2 v = u.2 v - u'.2 v := rfl
theorem one_fst_apply (w : InfinitePlace F) : (1 : 𝔸).1 w = 1 := rfl
theorem one_snd_apply (v : HeightOneSpectrum (𝓞 F)) : (1 : 𝔸).2 v = 1 := rfl

theorem adele_ext {u u' : 𝔸} (h1 : ∀ w, u.1 w = u'.1 w) (h2 : ∀ v, u.2 v = u'.2 v) : u = u' :=
  Prod.ext (funext h1) (Subtype.ext (funext h2))

theorem selRel (a : 𝔸∞) (b : 𝔸f) : SelRel (selE F a b) (selY F a b) (selZ F a b) (toAdele' F a b) where
  idem := adele_ext F (fun w => by rw [mul_fst_apply, selE_fst]; split_ifs <;> simp)
    (fun v => by rw [mul_snd_apply, selE_snd]; split_ifs <;> simp)
  yz := adele_ext F
    (fun w => by
      rw [mul_fst_apply, selY_fst, selZ_fst, one_fst_apply]
      split_ifs with h
      · exact mul_inv_cancel₀ (ne_zero_of_bigInf F h)
      · exact mul_one 1)
    (fun v => by
      rw [mul_snd_apply, selY_snd, selZ_snd, one_snd_apply]
      split_ifs with h
      · exact mul_inv_cancel₀ (ne_zero_of_bigFin F h)
      · exact mul_one 1)
  small := adele_ext F
    (fun w => by rw [mul_fst_apply, sub_fst_apply, one_fst_apply, selE_fst, selY_fst]; split_ifs <;> simp)
    (fun v => by rw [mul_snd_apply, sub_snd_apply, one_snd_apply, selE_snd, selY_snd]; split_ifs <;> simp)
  big := adele_ext F
    (fun w => by rw [mul_fst_apply, mul_fst_apply, selE_fst, selY_fst, toAdele'_fst]; split_ifs <;> simp)
    (fun v => by rw [mul_snd_apply, mul_snd_apply, selE_snd, selY_snd, toAdele'_snd]; split_ifs <;> simp)

theorem adelicWeyl_inv' : (adelicWeyl (𝓞 F) F)⁻¹ = adelicWeyl (𝓞 F) F := by
  rw [adelicWeyl, ← map_inv, gl2Weyl_inv]

theorem coe_adelicWeyl_mul_unipotent (u : 𝔸) :
    (((adelicWeyl (𝓞 F) F)⁻¹ * unipotentGL2 u : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) 𝔸) = !![0, 1; 1, u] := by
  rw [adelicWeyl_inv', Matrix.GeneralLinearGroup.coe_mul, unipotentGL2_coe]
  have hw : ((adelicWeyl (𝓞 F) F : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) 𝔸) = !![0, 1; 1, 0] := by
    ext i j
    rw [adelicWeyl, globalPoints_apply]
    fin_cases i <;> fin_cases j <;> simp [gl2Weyl]
  rw [hw]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

def mFactor (a : 𝔸∞) (b : 𝔸f) : AdelicGL2 (𝓞 F) F :=
  (bFactor (selRel F a b))⁻¹ * ((adelicWeyl (𝓞 F) F)⁻¹ * unipotentGL2 (toAdele' F a b))

theorem weyl_unipotent_eq (u : 𝔸) :
    (adelicWeyl (𝓞 F) F)⁻¹ * unipotentGL2 u = bFactor (selRel F u.1 u.2) * mFactor F u.1 u.2 := by
  rw [mFactor, mul_inv_cancel_left]; rfl

theorem coe_mFactor (a : 𝔸∞) (b : 𝔸f) : ((mFactor F a b : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) 𝔸) =
    mMat (selE F a b) (selZ F a b) (toAdele' F a b) := by
  rw [mFactor, Matrix.GeneralLinearGroup.coe_mul, coe_adelicWeyl_mul_unipotent, ← bMat_mul_mMat (selRel F a b),
    ← Matrix.mul_assoc, Matrix.GeneralLinearGroup.coe_inv, coe_bFactor, Matrix.nonsing_inv_mul _ (isUnit_det_bMat (selRel F a b)),
    Matrix.one_mul]

theorem coe_mFactor_inv (a : 𝔸∞) (b : 𝔸f) : (((mFactor F a b)⁻¹ : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) 𝔸) =
    mInvMat (selE F a b) (selZ F a b) (toAdele' F a b) := by
  rw [Matrix.GeneralLinearGroup.coe_inv, coe_mFactor]
  exact Matrix.inv_eq_right_inv (mMat_mul_mInvMat (selRel F a b))

end Adelic2
p2m_reactivate "P2MW.S_AutomorphicForm_weylIntertwiningIntegrand_finiteAdeleSlice_integrable_of_re_gt_half.AutomorphicForm P2MW.S_AutomorphicForm_weylIntertwiningIntegrand_finiteAdeleSlice_integrable_of_re_gt_half.AutomorphicForm.WeylIntegrable"

end AutomorphicForm.WeylIntegrable
p2m_reactivate "P2MW.S_AutomorphicForm_weylIntertwiningIntegrand_finiteAdeleSlice_integrable_of_re_gt_half.AutomorphicForm P2MW.S_AutomorphicForm_weylIntertwiningIntegrand_finiteAdeleSlice_integrable_of_re_gt_half.AutomorphicForm.WeylIntegrable"
p2m_reactivate "P2MW.S_AutomorphicForm_weylIntertwiningIntegrand_finiteAdeleSlice_integrable_of_re_gt_half.AutomorphicForm P2MW.S_AutomorphicForm_weylIntertwiningIntegrand_finiteAdeleSlice_integrable_of_re_gt_half.AutomorphicForm.WeylIntegrable"

end
p2m_reactivate "P2MW.S_AutomorphicForm_weylIntertwiningIntegrand_finiteAdeleSlice_integrable_of_re_gt_half.AutomorphicForm P2MW.S_AutomorphicForm_weylIntertwiningIntegrand_finiteAdeleSlice_integrable_of_re_gt_half.AutomorphicForm.WeylIntegrable"

noncomputable section

open NumberField NumberField.AdelicBox IsDedekindDomain
open scoped Classical

namespace AutomorphicForm
p2m_export "AutomorphicForm" "IsInducedSection borelSubgroup borelDiagFst borelDiagSnd globalPoints_apply AdelicGL2 IsUnitaryChar unipotentGL2 unipotentGL2_coe unipotentGL2_zero unipotentGL2_add norm_cpowChar_apply etaFst etaSnd etaFst_apply etaSnd_apply gl2Weyl gl2Weyl_inv adelicWeyl"
namespace WeylIntegrable
p2m_open "AutomorphicForm"

section EntryBox

variable {A : Type*} [CommRing A]

def matBox (C : Set A) : Set (Matrix (Fin 2) (Fin 2) A) := {M | ∀ i j, M i j ∈ C}

omit [CommRing A] in
theorem isCompact_matBox [TopologicalSpace A] {C : Set A} (hC : IsCompact C) : IsCompact (matBox C) := by
  have : matBox C = Set.pi Set.univ fun _ : Fin 2 => Set.pi Set.univ fun _ : Fin 2 => C := by
    ext M; exact ⟨fun h i _ j _ => h i j, fun h i j => h i (Set.mem_univ _) j (Set.mem_univ _)⟩
  rw [this]
  exact isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => hC

def unitBox (C : Set A) : Set (GL (Fin 2) A) := {k | (k : Matrix (Fin 2) (Fin 2) A) ∈ matBox C ∧ ((k⁻¹ : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) ∈ matBox C}

theorem unitBox_eq_preimage (C : Set A) :
    unitBox C = Units.embedProduct (Matrix (Fin 2) (Fin 2) A) ⁻¹' (matBox C ×ˢ (MulOpposite.op '' matBox C)) := by
  ext k
  simp only [unitBox, Set.mem_setOf_eq, Set.mem_preimage, Units.embedProduct_apply, Set.mem_prod, Set.mem_image]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨h1, _, h2, rfl⟩
  · rintro ⟨h1, M, hM, hMk⟩
    refine ⟨h1, ?_⟩
    have : M = ((k⁻¹ : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) := MulOpposite.op_injective hMk
    rwa [← this]

theorem isCompact_unitBox [TopologicalSpace A] [IsTopologicalRing A] [T1Space A] {C : Set A} (hC : IsCompact C) :
    IsCompact (unitBox C) := by
  rw [unitBox_eq_preimage]
  exact Units.isClosedEmbedding_embedProduct.isCompact_preimage
    ((isCompact_matBox hC).prod ((isCompact_matBox hC).image MulOpposite.continuous_op))

theorem exists_bound_on_unitBox [TopologicalSpace A] [IsTopologicalRing A] [T1Space A] {C : Set A} (hC : IsCompact C)
    {φ : GL (Fin 2) A → ℂ} (hφ : Continuous φ) (g : GL (Fin 2) A) : ∃ B : ℝ, ∀ k ∈ unitBox C, ‖φ (k * g)‖ ≤ B :=
  (isCompact_unitBox hC).exists_bound_of_continuousOn (hφ.comp (continuous_id.mul continuous_const)).continuousOn

end EntryBox
p2m_reactivate "P2MW.S_AutomorphicForm_weylIntertwiningIntegrand_finiteAdeleSlice_integrable_of_re_gt_half.AutomorphicForm P2MW.S_AutomorphicForm_weylIntertwiningIntegrand_finiteAdeleSlice_integrable_of_re_gt_half.AutomorphicForm.WeylIntegrable"

section NormBounds

variable {R : Type*} [NormedRing R]

theorem norm_mul_le_of_le {a b : R} {s t : ℝ} (ha : ‖a‖ ≤ s) (hb : ‖b‖ ≤ t) (hs : 0 ≤ s) : ‖a * b‖ ≤ s * t :=
  (norm_mul_le a b).trans (mul_le_mul ha hb (norm_nonneg _) hs)

theorem entry_bounds [NormOneClass R] {e z p : R} (he : ‖e‖ ≤ 1) (hz : ‖z‖ ≤ 1) (hp : ‖p‖ ≤ 1) :
    ‖e‖ ≤ 9 ∧ ‖1 - e‖ ≤ 9 ∧ ‖1 - e + e * z‖ ≤ 9 ∧ ‖p + e‖ ≤ 9 ∧
    ‖(2 * e - 1) * (p + e)‖ ≤ 9 ∧ ‖-((2 * e - 1) * (1 - e))‖ ≤ 9 ∧ ‖-((2 * e - 1) * (1 - e + e * z))‖ ≤ 9 ∧ ‖(2 * e - 1) * e‖ ≤ 9 := by
  have h1 : ‖(1 : R)‖ ≤ 1 := norm_one.le
  have h1e : ‖1 - e‖ ≤ 2 := (norm_sub_le_of_le h1 he).trans (by norm_num)
  have hsel : ‖2 * e - 1‖ ≤ 3 := by rw [two_mul]; exact (norm_sub_le_of_le (norm_add_le_of_le he he) h1).trans (by norm_num)
  have h3 : ‖1 - e + e * z‖ ≤ 3 := (norm_add_le_of_le h1e (norm_mul_le_of_le he hz zero_le_one)).trans (by norm_num)
  have h4 : ‖p + e‖ ≤ 2 := (norm_add_le_of_le hp he).trans (by norm_num)
  refine ⟨he.trans (by norm_num), h1e.trans (by norm_num), h3.trans (by norm_num), h4.trans (by norm_num), ?_, ?_, ?_, ?_⟩
  · exact (norm_mul_le_of_le hsel h4 (by norm_num)).trans (by norm_num)
  · rw [norm_neg]; exact (norm_mul_le_of_le hsel h1e (by norm_num)).trans (by norm_num)
  · rw [norm_neg]; exact (norm_mul_le_of_le hsel h3 (by norm_num)).trans (by norm_num)
  · exact (norm_mul_le_of_le hsel he (by norm_num)).trans (by norm_num)

end NormBounds
p2m_reactivate "P2MW.S_AutomorphicForm_weylIntertwiningIntegrand_finiteAdeleSlice_integrable_of_re_gt_half.AutomorphicForm P2MW.S_AutomorphicForm_weylIntertwiningIntegrand_finiteAdeleSlice_integrable_of_re_gt_half.AutomorphicForm.WeylIntegrable"

section AdelicBoxSec

variable (F : Type) [Field F] [NumberField F]

local notation "𝔸" => AdeleRing (𝓞 F) F
local notation "𝔸∞" => InfiniteAdeleRing F
local notation "𝔸f" => FiniteAdeleRing (𝓞 F) F

def archBall : Set 𝔸∞ := {a | ∀ w, ‖a w‖ ≤ 9}

omit [NumberField F] in
theorem isCompact_archBall : IsCompact (archBall F) := by
  haveI := fun w => AdelicBox.properSpace_completion F w
  have : archBall F = Set.pi Set.univ fun w : InfinitePlace F => Metric.closedBall (0 : w.Completion) 9 := by
    ext a; exact ⟨fun h w _ => mem_closedBall_zero_iff.mpr (h w), fun h w => mem_closedBall_zero_iff.mp (h w (Set.mem_univ _))⟩
  rw [this]
  exact isCompact_univ_pi fun w => isCompact_closedBall _ _

def entrySet : Set 𝔸 := slab F (archBall F) (integralFiniteAdeles (𝓞 F) F)

theorem isCompact_entrySet : IsCompact (entrySet F) := by
  have : entrySet F = (fun p : 𝔸∞ × 𝔸f => (p : 𝔸)) '' (archBall F ×ˢ integralFiniteAdeles (𝓞 F) F) := by
    ext x; simp only [entrySet, mem_slab]
    exact ⟨fun ⟨h1, h2⟩ => ⟨(x.1, x.2), ⟨h1, h2⟩, rfl⟩, by rintro ⟨p, ⟨h1, h2⟩, rfl⟩; exact ⟨h1, h2⟩⟩
  rw [this]
  exact ((isCompact_archBall F).prod (isCompact_integralFiniteAdeles F)).image continuous_id

theorem mem_entrySet {u : 𝔸} : u ∈ entrySet F ↔ (∀ w, ‖u.1 w‖ ≤ 9) ∧ ∀ v, u.2 v ∈ v.adicCompletionIntegers F := Iff.rfl

def cInf (w : InfinitePlace F) : 𝔸 →+* w.Completion := (Pi.evalRingHom _ w).comp (RingHom.fst 𝔸∞ 𝔸f)

def cFin (v : HeightOneSpectrum (𝓞 F)) : 𝔸 →+* v.adicCompletion F where
  toFun u := u.2 v
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

theorem cInf_apply (w : InfinitePlace F) (u : 𝔸) : cInf F w u = u.1 w := rfl
theorem cFin_apply (v : HeightOneSpectrum (𝓞 F)) (u : 𝔸) : cFin F v u = u.2 v := rfl

theorem norm_selE_le (a : 𝔸∞) (b : 𝔸f) (w : InfinitePlace F) : ‖(selE F a b).1 w‖ ≤ 1 := by
  rw [selE_fst]; split_ifs <;> simp

theorem norm_selZ_le (a : 𝔸∞) (b : 𝔸f) (w : InfinitePlace F) : ‖(selZ F a b).1 w‖ ≤ 1 := by
  rw [selZ_fst]; split_ifs with h
  · exact (norm_inv_lt_one_of_bigInf F h).le
  · simp

theorem norm_selP_le (a : 𝔸∞) (b : 𝔸f) (w : InfinitePlace F) : ‖((1 - selE F a b) * toAdele' F a b).1 w‖ ≤ 1 := by
  rw [mul_fst_apply, sub_fst_apply, one_fst_apply, selE_fst, toAdele'_fst]
  split_ifs with h
  · simp
  · rw [BigInf, not_lt] at h; simpa using h

theorem selE_mem (a : 𝔸∞) (b : 𝔸f) (v : HeightOneSpectrum (𝓞 F)) : (selE F a b).2 v ∈ v.adicCompletionIntegers F := by
  rw [selE_snd]; split_ifs
  · exact one_mem _
  · exact zero_mem _

theorem selZ_mem (a : 𝔸∞) (b : 𝔸f) (v : HeightOneSpectrum (𝓞 F)) : (selZ F a b).2 v ∈ v.adicCompletionIntegers F := by
  rw [selZ_snd]; split_ifs with h
  · exact inv_mem_of_bigFin F h
  · exact one_mem _

theorem selP_mem (a : 𝔸∞) (b : 𝔸f) (v : HeightOneSpectrum (𝓞 F)) :
    ((1 - selE F a b) * toAdele' F a b).2 v ∈ v.adicCompletionIntegers F := by
  rw [mul_snd_apply, sub_snd_apply, one_snd_apply, selE_snd, toAdele'_snd]
  split_ifs with h
  · simp
  · rw [BigFin, not_not] at h; simpa using h

theorem entries_mem (ε z p : 𝔸)
    (hInf : ∀ w, ‖ε.1 w‖ ≤ 1 ∧ ‖z.1 w‖ ≤ 1 ∧ ‖p.1 w‖ ≤ 1)
    (hFin : ∀ v, ε.2 v ∈ v.adicCompletionIntegers F ∧ z.2 v ∈ v.adicCompletionIntegers F ∧ p.2 v ∈ v.adicCompletionIntegers F) :
    ε ∈ entrySet F ∧ 1 - ε ∈ entrySet F ∧ 1 - ε + ε * z ∈ entrySet F ∧ p + ε ∈ entrySet F ∧
    (2 * ε - 1) * (p + ε) ∈ entrySet F ∧ -((2 * ε - 1) * (1 - ε)) ∈ entrySet F ∧
    -((2 * ε - 1) * (1 - ε + ε * z)) ∈ entrySet F ∧ (2 * ε - 1) * ε ∈ entrySet F := by

  have I : ∀ (u : 𝔸), (∀ w, ‖cInf F w u‖ ≤ 9) → (∀ v, cFin F v u ∈ v.adicCompletionIntegers F) → u ∈ entrySet F :=
    fun u h1 h2 => (mem_entrySet F).mpr ⟨h1, h2⟩
  have two : ∀ v, (2 : v.adicCompletion F) * cFin F v ε - 1 ∈ v.adicCompletionIntegers F := fun v => by
    rw [two_mul]; exact sub_mem (add_mem (hFin v).1 (hFin v).1) (one_mem _)
  have B : ∀ w, _ := fun w => entry_bounds (hInf w).1 (hInf w).2.1 (hInf w).2.2
  refine ⟨I _ (fun w => ?_) (fun v => ?_), I _ (fun w => ?_) (fun v => ?_), I _ (fun w => ?_) (fun v => ?_), I _ (fun w => ?_) (fun v => ?_),
    I _ (fun w => ?_) (fun v => ?_), I _ (fun w => ?_) (fun v => ?_), I _ (fun w => ?_) (fun v => ?_), I _ (fun w => ?_) (fun v => ?_)⟩
  · simpa only [cInf_apply] using (B w).1
  · simpa only [cFin_apply] using (hFin v).1
  · simpa only [map_sub, map_one, cInf_apply] using (B w).2.1
  · simpa only [map_sub, map_one, cFin_apply] using sub_mem (one_mem _) (hFin v).1
  · simpa only [map_add, map_sub, map_mul, map_one, cInf_apply] using (B w).2.2.1
  · simpa only [map_add, map_sub, map_mul, map_one, cFin_apply] using add_mem (sub_mem (one_mem _) (hFin v).1) (mul_mem (hFin v).1 (hFin v).2.1)
  · simpa only [map_add, cInf_apply] using (B w).2.2.2.1
  · simpa only [map_add, cFin_apply] using add_mem (hFin v).2.2 (hFin v).1
  · simpa only [map_add, map_sub, map_mul, map_one, map_ofNat, cInf_apply] using (B w).2.2.2.2.1
  · simpa only [map_add, map_sub, map_mul, map_one, map_ofNat, cFin_apply] using mul_mem (two v) (add_mem (hFin v).2.2 (hFin v).1)
  · simpa only [map_neg, map_sub, map_mul, map_one, map_ofNat, cInf_apply] using (B w).2.2.2.2.2.1
  · simpa only [map_neg, map_sub, map_mul, map_one, map_ofNat, cFin_apply] using neg_mem (mul_mem (two v) (sub_mem (one_mem _) (hFin v).1))
  · simpa only [map_neg, map_add, map_sub, map_mul, map_one, map_ofNat, cInf_apply] using (B w).2.2.2.2.2.2.1
  · simpa only [map_neg, map_add, map_sub, map_mul, map_one, map_ofNat, cFin_apply] using
      neg_mem (mul_mem (two v) (add_mem (sub_mem (one_mem _) (hFin v).1) (mul_mem (hFin v).1 (hFin v).2.1)))
  · simpa only [map_sub, map_mul, map_one, map_ofNat, cInf_apply] using (B w).2.2.2.2.2.2.2
  · simpa only [map_sub, map_mul, map_one, map_ofNat, cFin_apply] using mul_mem (two v) (hFin v).1

theorem mFactor_mem_unitBox (a : 𝔸∞) (b : 𝔸f) : mFactor F a b ∈ unitBox (entrySet F) := by
  obtain ⟨m1, m2, m3, m4, i1, i2, i3, i4⟩ := entries_mem F (selE F a b) (selZ F a b) ((1 - selE F a b) * toAdele' F a b)
    (fun w => ⟨norm_selE_le F a b w, norm_selZ_le F a b w, norm_selP_le F a b w⟩)
    (fun v => ⟨selE_mem F a b v, selZ_mem F a b v, selP_mem F a b v⟩)
  constructor
  · intro i j
    rw [coe_mFactor]
    fin_cases i <;> fin_cases j
    · exact m1
    · exact m2
    · exact m3
    · exact m4
  · intro i j
    rw [coe_mFactor_inv]
    fin_cases i <;> fin_cases j
    · exact i1
    · exact i2
    · exact i3
    · exact i4

theorem exists_bound_mFactor {φ : AdelicGL2 (𝓞 F) F → ℂ} (hφ : Continuous φ) (g : AdelicGL2 (𝓞 F) F) :
    ∃ B : ℝ, ∀ (a : 𝔸∞) (b : 𝔸f), ‖φ (mFactor F a b * g)‖ ≤ B := by
  letI : TopologicalSpace 𝔸 := inferInstance
  obtain ⟨B, hB⟩ := exists_bound_on_unitBox (isCompact_entrySet F) hφ g
  exact ⟨B, fun a b => hB _ (mFactor_mem_unitBox F a b)⟩

end AdelicBoxSec
p2m_reactivate "P2MW.S_AutomorphicForm_weylIntertwiningIntegrand_finiteAdeleSlice_integrable_of_re_gt_half.AutomorphicForm P2MW.S_AutomorphicForm_weylIntertwiningIntegrand_finiteAdeleSlice_integrable_of_re_gt_half.AutomorphicForm.WeylIntegrable"

end AutomorphicForm.WeylIntegrable
p2m_reactivate "P2MW.S_AutomorphicForm_weylIntertwiningIntegrand_finiteAdeleSlice_integrable_of_re_gt_half.AutomorphicForm P2MW.S_AutomorphicForm_weylIntertwiningIntegrand_finiteAdeleSlice_integrable_of_re_gt_half.AutomorphicForm.WeylIntegrable"
p2m_reactivate "P2MW.S_AutomorphicForm_weylIntertwiningIntegrand_finiteAdeleSlice_integrable_of_re_gt_half.AutomorphicForm P2MW.S_AutomorphicForm_weylIntertwiningIntegrand_finiteAdeleSlice_integrable_of_re_gt_half.AutomorphicForm.WeylIntegrable"

end
p2m_reactivate "P2MW.S_AutomorphicForm_weylIntertwiningIntegrand_finiteAdeleSlice_integrable_of_re_gt_half.AutomorphicForm P2MW.S_AutomorphicForm_weylIntertwiningIntegrand_finiteAdeleSlice_integrable_of_re_gt_half.AutomorphicForm.WeylIntegrable"

noncomputable section

open NumberField IsDedekindDomain
open scoped Classical

namespace AutomorphicForm
p2m_export "AutomorphicForm" "IsInducedSection borelSubgroup borelDiagFst borelDiagSnd globalPoints_apply AdelicGL2 IsUnitaryChar unipotentGL2 unipotentGL2_coe unipotentGL2_zero unipotentGL2_add norm_cpowChar_apply etaFst etaSnd etaFst_apply etaSnd_apply gl2Weyl gl2Weyl_inv adelicWeyl"
namespace WeylIntegrable
p2m_open "AutomorphicForm"

section PositiveChar

variable {G : Type*} [Group G]

theorem val_eq_one_of_mul_self_eq_one (α : G →* ℝˣ) (hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ)) {e : G} (he : e * e = 1) :
    ((α e : ℝˣ) : ℝ) = 1 := by
  have h : ((α e : ℝˣ) : ℝ) * ((α e : ℝˣ) : ℝ) = 1 := by rw [← Units.val_mul, ← map_mul, he, map_one, Units.val_one]
  rcases mul_self_eq_one_iff.mp h with h1 | h1
  · exact h1
  · exact absurd (hα e) (by rw [h1]; norm_num)

end PositiveChar
p2m_reactivate "P2MW.S_AutomorphicForm_weylIntertwiningIntegrand_finiteAdeleSlice_integrable_of_re_gt_half.AutomorphicForm P2MW.S_AutomorphicForm_weylIntertwiningIntegrand_finiteAdeleSlice_integrable_of_re_gt_half.AutomorphicForm.WeylIntegrable"

section Pointwise

variable (F : Type) [Field F] [NumberField F]

local notation "𝔸" => AdeleRing (𝓞 F) F
local notation "𝔸∞" => InfiniteAdeleRing F
local notation "𝔸f" => FiniteAdeleRing (𝓞 F) F

theorem apply_weyl_unipotent_eq (α : (𝔸)ˣ →* ℝˣ) (hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ)) (μ ν : (𝔸)ˣ →* ℂˣ) (s : ℂ)
    (φ : AdelicGL2 (𝓞 F) F → ℂ) (hφ : IsInducedSection (𝓞 F) F (etaFst μ α hα s) (etaSnd ν α hα s) φ) (u : 𝔸) (g : AdelicGL2 (𝓞 F) F) :
    φ ((adelicWeyl (𝓞 F) F)⁻¹ * unipotentGL2 u * g) =
      ((etaFst μ α hα s (eUnit (selRel F u.1 u.2) * (yUnit (selRel F u.1 u.2))⁻¹) : ℂˣ) : ℂ) *
        ((etaSnd ν α hα s (yUnit (selRel F u.1 u.2)) : ℂˣ) : ℂ) * φ (mFactor F u.1 u.2 * g) := by
  rw [weyl_unipotent_eq F u, mul_assoc, hφ _ (bFactor_mem_borel (selRel F u.1 u.2)) (mFactor F u.1 u.2 * g),
    borelDiagFst_bFactor, borelDiagSnd_bFactor]

theorem norm_apply_weyl_unipotent_eq (α : (𝔸)ˣ →* ℝˣ) (hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ)) (μ ν : (𝔸)ˣ →* ℂˣ) (s : ℂ)
    (φ : AdelicGL2 (𝓞 F) F → ℂ) (hμ : IsUnitaryChar (𝓞 F) F μ) (hν : IsUnitaryChar (𝓞 F) F ν)
    (hφ : IsInducedSection (𝓞 F) F (etaFst μ α hα s) (etaSnd ν α hα s) φ) (u : 𝔸) (g : AdelicGL2 (𝓞 F) F) :
    ‖φ ((adelicWeyl (𝓞 F) F)⁻¹ * unipotentGL2 u * g)‖ =
      ((α (yUnit (selRel F u.1 u.2)) : ℝˣ) : ℝ) ^ (-(2 * s.re + 1)) * ‖φ (mFactor F u.1 u.2 * g)‖ := by
  set h := selRel F u.1 u.2
  set t : ℝ := ((α (yUnit h) : ℝˣ) : ℝ) with ht
  have htpos : 0 < t := hα _
  have he : ((α (eUnit h) : ℝˣ) : ℝ) = 1 := val_eq_one_of_mul_self_eq_one α hα (eUnit_mul_self h)
  have h1 : ‖((etaFst μ α hα s (eUnit h * (yUnit h)⁻¹) : ℂˣ) : ℂ)‖ = t⁻¹ ^ (s.re + 1 / 2) := by
    rw [etaFst_apply, Units.val_mul, norm_mul, hμ, one_mul, norm_cpowChar_apply, map_mul, map_inv, Units.val_mul, he, one_mul,
      Units.val_inv_eq_inv_val, ← ht]
    norm_num
  have h2 : ‖(((etaSnd ν α hα s (yUnit h)) : ℂˣ) : ℂ)‖ = t ^ (-(s.re + 1 / 2)) := by
    rw [etaSnd_apply, Units.val_mul, norm_mul, hν, one_mul, norm_cpowChar_apply, ← ht]
    norm_num
  rw [apply_weyl_unipotent_eq F α hα μ ν s φ hφ u g, norm_mul, norm_mul, h1, h2, Real.inv_rpow htpos.le, ← Real.rpow_neg htpos.le,
    ← Real.rpow_add htpos]
  congr 2
  ring

theorem norm_apply_weyl_unipotent_le (α : (𝔸)ˣ →* ℝˣ) (hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ)) (μ ν : (𝔸)ˣ →* ℂˣ) (s : ℂ)
    (φ : AdelicGL2 (𝓞 F) F → ℂ) (hμ : IsUnitaryChar (𝓞 F) F μ) (hν : IsUnitaryChar (𝓞 F) F ν)
    (hφ : IsInducedSection (𝓞 F) F (etaFst μ α hα s) (etaSnd ν α hα s) φ) (hφc : Continuous φ) (g : AdelicGL2 (𝓞 F) F) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ u : 𝔸, ‖φ ((adelicWeyl (𝓞 F) F)⁻¹ * unipotentGL2 u * g)‖ ≤
      B * ((α (yUnit (selRel F u.1 u.2)) : ℝˣ) : ℝ) ^ (-(2 * s.re + 1)) := by
  obtain ⟨B, hB⟩ := exists_bound_mFactor F hφc g
  refine ⟨max B 0, le_max_right _ _, fun u => ?_⟩
  rw [norm_apply_weyl_unipotent_eq F α hα μ ν s φ hμ hν hφ u g, mul_comm]
  exact mul_le_mul_of_nonneg_right ((hB u.1 u.2).trans (le_max_left _ _)) (Real.rpow_nonneg (hα _).le _)

end Pointwise
p2m_reactivate "P2MW.S_AutomorphicForm_weylIntertwiningIntegrand_finiteAdeleSlice_integrable_of_re_gt_half.AutomorphicForm P2MW.S_AutomorphicForm_weylIntertwiningIntegrand_finiteAdeleSlice_integrable_of_re_gt_half.AutomorphicForm.WeylIntegrable"

end AutomorphicForm.WeylIntegrable
p2m_reactivate "P2MW.S_AutomorphicForm_weylIntertwiningIntegrand_finiteAdeleSlice_integrable_of_re_gt_half.AutomorphicForm P2MW.S_AutomorphicForm_weylIntertwiningIntegrand_finiteAdeleSlice_integrable_of_re_gt_half.AutomorphicForm.WeylIntegrable"
p2m_reactivate "P2MW.S_AutomorphicForm_weylIntertwiningIntegrand_finiteAdeleSlice_integrable_of_re_gt_half.AutomorphicForm P2MW.S_AutomorphicForm_weylIntertwiningIntegrand_finiteAdeleSlice_integrable_of_re_gt_half.AutomorphicForm.WeylIntegrable"

end
p2m_reactivate "P2MW.S_AutomorphicForm_weylIntertwiningIntegrand_finiteAdeleSlice_integrable_of_re_gt_half.AutomorphicForm P2MW.S_AutomorphicForm_weylIntertwiningIntegrand_finiteAdeleSlice_integrable_of_re_gt_half.AutomorphicForm.WeylIntegrable"

noncomputable section

open NumberField NumberField.AdelicBox IsDedekindDomain IsDedekindDomain.HeightOneSpectrum WithZero
open scoped Classical

namespace AutomorphicForm
p2m_export "AutomorphicForm" "IsInducedSection borelSubgroup borelDiagFst borelDiagSnd globalPoints_apply AdelicGL2 IsUnitaryChar unipotentGL2 unipotentGL2_coe unipotentGL2_zero unipotentGL2_add norm_cpowChar_apply etaFst etaSnd etaFst_apply etaSnd_apply gl2Weyl gl2Weyl_inv adelicWeyl"
namespace WeylIntegrable
p2m_open "AutomorphicForm"

section Lattices

variable (F : Type) [Field F] [NumberField F]

local notation "𝔸f" => FiniteAdeleRing (𝓞 F) F
local notation "HOS" => HeightOneSpectrum (𝓞 F)

theorem fa_mul_apply (a b : 𝔸f) (v : HOS) : (a * b) v = a v * b v := rfl

theorem mem_intLattice_iff (t : 𝔸f) : t ∈ intLattice F ↔ ∀ v, Valued.v (t v) ≤ 1 := Iff.rfl

theorem mem_integralFiniteAdeles_iff' (t : 𝔸f) : t ∈ integralFiniteAdeles (𝓞 F) F ↔ ∀ v, Valued.v (t v) ≤ 1 := Iff.rfl

theorem valued_ne_zero_of_unit (y : (𝔸f)ˣ) (v : HOS) : Valued.v ((y : 𝔸f) v) ≠ 0 := by
  intro h
  have h1 : Valued.v (((y : 𝔸f) * ((y⁻¹ : (𝔸f)ˣ) : 𝔸f)) v) = 1 := by rw [Units.mul_inv]; exact map_one _
  rw [fa_mul_apply, map_mul, h, zero_mul] at h1
  exact zero_ne_one h1

theorem apply_ne_zero_of_unit (y : (𝔸f)ˣ) (v : HOS) : (y : 𝔸f) v ≠ 0 := fun h =>
  valued_ne_zero_of_unit F y v (by rw [h, map_zero])

theorem mem_dilate_iff (y : (𝔸f)ˣ) (t : 𝔸f) : t ∈ dilate F y ↔ ∀ v, Valued.v (t v) ≤ Valued.v ((y : 𝔸f) v) := by
  rw [← SetLike.mem_coe, coe_dilate, Set.mem_smul_set]
  constructor
  · rintro ⟨s, hs, rfl⟩ v
    rw [smul_eq_mul, fa_mul_apply, map_mul]
    exact mul_le_of_le_one_right' ((mem_integralFiniteAdeles_iff' F s).mp hs v)
  · intro h
    refine ⟨((y⁻¹ : (𝔸f)ˣ) : 𝔸f) * t, (mem_integralFiniteAdeles_iff' F _).mpr fun v => ?_, ?_⟩
    · rw [fa_mul_apply, map_mul]
      have hy := valued_ne_zero_of_unit F y v
      have hyv : (y : 𝔸f) v * ((y⁻¹ : (𝔸f)ˣ) : 𝔸f) v = 1 := by rw [← fa_mul_apply, Units.mul_inv]; rfl
      have hinv : Valued.v (((y⁻¹ : (𝔸f)ˣ) : 𝔸f) v) = (Valued.v ((y : 𝔸f) v))⁻¹ := by
        rw [← inv_eq_of_mul_eq_one_right hyv, map_inv₀]
      rw [hinv]
      calc (Valued.v ((y : 𝔸f) v))⁻¹ * Valued.v (t v) ≤ (Valued.v ((y : 𝔸f) v))⁻¹ * Valued.v ((y : 𝔸f) v) :=
            mul_le_mul' le_rfl (h v)
        _ = 1 := inv_mul_cancel₀ hy
    · show (y : 𝔸f) * (((y⁻¹ : (𝔸f)ˣ) : 𝔸f) * t) = t
      rw [← mul_assoc, Units.mul_inv, one_mul]

theorem intLattice_le_dilate {y : (𝔸f)ˣ} (hy : ∀ v, 1 ≤ Valued.v ((y : 𝔸f) v)) : intLattice F ≤ dilate F y := fun t ht =>
  (mem_dilate_iff F y t).mpr fun v => (((mem_intLattice_iff F t).mp ht v).trans (hy v))

theorem isCompact_dilate (y : (𝔸f)ˣ) : IsCompact (dilate F y : Set 𝔸f) := by
  rw [coe_dilate]
  exact (isCompact_integralFiniteAdeles F).image (continuous_const.mul continuous_id)

theorem relIndex_dilate_ne_zero (y : (𝔸f)ˣ) : (intLattice F).relIndex (dilate F y) ≠ 0 := by
  haveI : CompactSpace (dilate F y) := isCompact_iff_compactSpace.mp (isCompact_dilate F y)
  have hopen : IsOpen (((intLattice F).addSubgroupOf (dilate F y) : AddSubgroup (dilate F y)) : Set (dilate F y)) :=
    (isOpen_integralFiniteAdeles F).preimage continuous_subtype_val
  haveI := AddSubgroup.quotient_finite_of_isOpen _ hopen
  exact AddSubgroup.index_ne_zero_of_finite

def unif (v : HOS) : F := Classical.choose (v.valuation_exists_uniformizer F)

theorem valuation_unif (v : HOS) : v.valuation F (unif F v) = exp (-1 : ℤ) := Classical.choose_spec (v.valuation_exists_uniformizer F)

theorem valued_unif (v : HOS) : Valued.v ((unif F v : F) : v.adicCompletion F) = exp (-1 : ℤ) := by
  rw [valuedAdicCompletion_eq_valuation', valuation_unif]

theorem unif_coe_ne_zero (v : HOS) : ((unif F v : F) : v.adicCompletion F) ≠ 0 := fun h => by
  have := valued_unif F v; rw [h, map_zero] at this; exact exp_ne_zero this.symm

def unifFun (k : HOS →₀ ℕ) (v : HOS) : v.adicCompletion F := ((unif F v : F) : v.adicCompletion F) ^ (-(k v : ℤ))

theorem valued_unifFun (k : HOS →₀ ℕ) (v : HOS) : Valued.v (unifFun F k v) = exp (k v : ℤ) := by
  rw [unifFun, map_zpow₀, valued_unif, ← exp_zsmul]; congr 1; ring

theorem unifFun_of_notMem (k : HOS →₀ ℕ) {v : HOS} (hv : v ∉ k.support) : unifFun F k v = 1 := by
  rw [unifFun, Finsupp.notMem_support_iff.mp hv]; simp

def unifIdele (k : HOS →₀ ℕ) : (𝔸f)ˣ where
  val := RestrictedProduct.mk (unifFun F k) (Filter.eventually_cofinite.mpr
    ((k.support.finite_toSet).subset fun v hv => by
      by_contra h; exact hv (by rw [unifFun_of_notMem F k h]; exact one_mem _)))
  inv := RestrictedProduct.mk (fun v => (unifFun F k v)⁻¹) (Filter.eventually_cofinite.mpr
    ((k.support.finite_toSet).subset fun v hv => by
      by_contra h; exact hv (by rw [unifFun_of_notMem F k h, inv_one]; exact one_mem _)))
  val_inv := Subtype.ext (funext fun v => mul_inv_cancel₀ (zpow_ne_zero _ (unif_coe_ne_zero F v)))
  inv_val := Subtype.ext (funext fun v => inv_mul_cancel₀ (zpow_ne_zero _ (unif_coe_ne_zero F v)))

theorem unifIdele_apply (k : HOS →₀ ℕ) (v : HOS) : ((unifIdele F k : (𝔸f)ˣ) : 𝔸f) v = unifFun F k v := rfl

theorem valued_unifIdele (k : HOS →₀ ℕ) (v : HOS) : Valued.v (((unifIdele F k : (𝔸f)ˣ) : 𝔸f) v) = exp (k v : ℤ) :=
  valued_unifFun F k v

def latt (k : HOS →₀ ℕ) : AddSubgroup 𝔸f := dilate F (unifIdele F k)

theorem mem_latt_iff (k : HOS →₀ ℕ) (t : 𝔸f) : t ∈ latt F k ↔ ∀ v, Valued.v (t v) ≤ exp (k v : ℤ) := by
  rw [latt, mem_dilate_iff]; simp only [valued_unifIdele]

theorem one_le_valued_unifIdele (k : HOS →₀ ℕ) (v : HOS) : 1 ≤ Valued.v (((unifIdele F k : (𝔸f)ˣ) : 𝔸f) v) := by
  rw [valued_unifIdele, ← exp_zero, exp_le_exp]; exact_mod_cast Nat.zero_le _

theorem intLattice_le_latt (k : HOS →₀ ℕ) : intLattice F ≤ latt F k := intLattice_le_dilate F (one_le_valued_unifIdele F k)

theorem latt_mono {k k' : HOS →₀ ℕ} (h : k ≤ k') : latt F k ≤ latt F k' := fun t ht =>
  (mem_latt_iff F k' t).mpr fun v => ((mem_latt_iff F k t).mp ht v).trans (exp_le_exp.mpr (by exact_mod_cast h v))

theorem relIndex_latt_ne_zero (k : HOS →₀ ℕ) : (intLattice F).relIndex (latt F k) ≠ 0 := relIndex_dilate_ne_zero F _

theorem isCompact_latt (k : HOS →₀ ℕ) : IsCompact (latt F k : Set 𝔸f) := isCompact_dilate F _

theorem dilate_eq_latt (y : (𝔸f)ˣ) (hy : ∀ v, 1 ≤ Valued.v ((y : 𝔸f) v)) :
    ∃ k : HOS →₀ ℕ, dilate F y = latt F k ∧ ∀ v, exp (k v : ℤ) = Valued.v ((y : 𝔸f) v) := by

  have hfin : {v : HOS | Valued.v ((y : 𝔸f) v) ≠ 1}.Finite := by
    refine ((show RestrictedProduct (fun v : HOS => v.adicCompletion F) (fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F)))
      Filter.cofinite from (y : 𝔸f)).eventually).subset fun v hv => ?_
    intro hint
    exact hv (le_antisymm ((mem_adicCompletionIntegers _ _ _).mp hint) (hy v))
  let f : HOS → ℕ := fun v => (log (Valued.v ((y : 𝔸f) v))).toNat
  have hf : ∀ v, exp (f v : ℤ) = Valued.v ((y : 𝔸f) v) := fun v => by
    have hne := valued_ne_zero_of_unit F y v
    have hlog : 0 ≤ log (Valued.v ((y : 𝔸f) v)) := by rw [← exp_le_exp, exp_log hne, exp_zero]; exact hy v
    simp only [f, Int.toNat_of_nonneg hlog, exp_log hne]
  have hsupp : f.support ⊆ {v : HOS | Valued.v ((y : 𝔸f) v) ≠ 1} := fun v hv h1 => by
    apply hv
    show (log (Valued.v ((y : 𝔸f) v))).toNat = 0
    rw [h1, log_one, Int.toNat_zero]
  refine ⟨Finsupp.ofSupportFinite f (hfin.subset hsupp), ?_, fun v => ?_⟩
  · ext t
    rw [mem_dilate_iff, mem_latt_iff]
    simp only [Finsupp.ofSupportFinite_coe, hf]
  · rw [Finsupp.ofSupportFinite_coe]; exact hf v

end Lattices
p2m_reactivate "P2MW.S_AutomorphicForm_weylIntertwiningIntegrand_finiteAdeleSlice_integrable_of_re_gt_half.AutomorphicForm P2MW.S_AutomorphicForm_weylIntertwiningIntegrand_finiteAdeleSlice_integrable_of_re_gt_half.AutomorphicForm.WeylIntegrable"

end AutomorphicForm.WeylIntegrable
p2m_reactivate "P2MW.S_AutomorphicForm_weylIntertwiningIntegrand_finiteAdeleSlice_integrable_of_re_gt_half.AutomorphicForm P2MW.S_AutomorphicForm_weylIntertwiningIntegrand_finiteAdeleSlice_integrable_of_re_gt_half.AutomorphicForm.WeylIntegrable"
p2m_reactivate "P2MW.S_AutomorphicForm_weylIntertwiningIntegrand_finiteAdeleSlice_integrable_of_re_gt_half.AutomorphicForm P2MW.S_AutomorphicForm_weylIntertwiningIntegrand_finiteAdeleSlice_integrable_of_re_gt_half.AutomorphicForm.WeylIntegrable"

end
p2m_reactivate "P2MW.S_AutomorphicForm_weylIntertwiningIntegrand_finiteAdeleSlice_integrable_of_re_gt_half.AutomorphicForm P2MW.S_AutomorphicForm_weylIntertwiningIntegrand_finiteAdeleSlice_integrable_of_re_gt_half.AutomorphicForm.WeylIntegrable"

noncomputable section

open NumberField NumberField.AdelicBox IsDedekindDomain IsDedekindDomain.HeightOneSpectrum WithZero
open scoped Classical

namespace AutomorphicForm
p2m_export "AutomorphicForm" "IsInducedSection borelSubgroup borelDiagFst borelDiagSnd globalPoints_apply AdelicGL2 IsUnitaryChar unipotentGL2 unipotentGL2_coe unipotentGL2_zero unipotentGL2_add norm_cpowChar_apply etaFst etaSnd etaFst_apply etaSnd_apply gl2Weyl gl2Weyl_inv adelicWeyl"
namespace WeylIntegrable
p2m_open "AutomorphicForm"

section R2

variable (F : Type) [Field F] [NumberField F]

local notation "𝔸f" => FiniteAdeleRing (𝓞 F) F
local notation "HOS" => HeightOneSpectrum (𝓞 F)

def singleFin (v₀ : HOS) (t : v₀.adicCompletion F) : 𝔸f :=
  show RestrictedProduct (fun v : HOS => v.adicCompletion F) (fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F)))
      Filter.cofinite from
    RestrictedProduct.mk (Pi.single v₀ t) (Filter.eventually_cofinite.mpr ((Set.finite_singleton v₀).subset fun v hv => by
      by_contra h
      exact hv (by rw [Pi.single_eq_of_ne h]; exact zero_mem _)))

theorem singleFin_apply (v₀ : HOS) (t : v₀.adicCompletion F) (v : HOS) : singleFin F v₀ t v = Pi.single v₀ t v := rfl

theorem singleFin_apply_same (v₀ : HOS) (t : v₀.adicCompletion F) : singleFin F v₀ t v₀ = t := by
  rw [singleFin_apply, Pi.single_eq_same]

theorem singleFin_apply_of_ne (v₀ : HOS) (t : v₀.adicCompletion F) {v : HOS} (h : v ≠ v₀) : singleFin F v₀ t v = 0 := by
  rw [singleFin_apply, Pi.single_eq_of_ne h]

theorem singleFin_sub (v₀ : HOS) (t t' : v₀.adicCompletion F) : singleFin F v₀ t - singleFin F v₀ t' = singleFin F v₀ (t - t') :=
  Subtype.ext (funext fun v => by
    show singleFin F v₀ t v - singleFin F v₀ t' v = singleFin F v₀ (t - t') v
    simp only [singleFin_apply, Pi.single_sub, Pi.sub_apply])

def toCompl (v₀ : HOS) : F →+* v₀.adicCompletion F :=
  algebraMap F (v₀.adicCompletion F)

theorem valued_toCompl (v₀ : HOS) (x : F) : Valued.v (toCompl F v₀ x) = v₀.valuation F x := valuedAdicCompletion_eq_valuation' v₀ x

def stepElt (k : HOS →₀ ℕ) (v₀ : HOS) (r : 𝓞 F) : 𝔸f := singleFin F v₀ (toCompl F v₀ ((r : F) * unif F v₀ ^ (-((k v₀ : ℤ) + 1))))

theorem valued_toCompl_mul_unif_zpow (k : HOS →₀ ℕ) (v₀ : HOS) (x : F) :
    Valued.v (toCompl F v₀ (x * unif F v₀ ^ (-((k v₀ : ℤ) + 1)))) = v₀.valuation F x * exp ((k v₀ : ℤ) + 1) := by
  rw [valued_toCompl, map_mul, map_zpow₀, valuation_unif, ← exp_zsmul]
  congr 2; ring

theorem valued_stepElt_same (k : HOS →₀ ℕ) (v₀ : HOS) (r : 𝓞 F) :
    Valued.v (stepElt F k v₀ r v₀) = v₀.valuation F (r : F) * exp ((k v₀ : ℤ) + 1) := by
  rw [stepElt, singleFin_apply_same, valued_toCompl_mul_unif_zpow]

theorem stepElt_mem (k : HOS →₀ ℕ) (v₀ : HOS) (r : 𝓞 F) : stepElt F k v₀ r ∈ latt F (k + Finsupp.single v₀ 1) := by
  rw [mem_latt_iff]
  intro v
  by_cases hv : v = v₀
  · subst hv
    rw [valued_stepElt_same, Finsupp.add_apply, Finsupp.single_eq_same]
    push_cast
    exact mul_le_of_le_one_left' (valuation_le_one v (r := r))
  · rw [stepElt, singleFin_apply_of_ne F _ _ hv, map_zero]; exact zero_le'

theorem sub_mem_asIdeal_of_stepElt_sub_mem (k : HOS →₀ ℕ) (v₀ : HOS) {r r' : 𝓞 F}
    (h : stepElt F k v₀ r - stepElt F k v₀ r' ∈ latt F k) : r - r' ∈ v₀.asIdeal := by
  rw [← valuation_lt_one_iff_mem (K := F), ← exp_zero]
  have hv := (mem_latt_iff F k _).mp h v₀
  rw [stepElt, stepElt, singleFin_sub, singleFin_apply_same, ← map_sub, ← sub_mul, valued_toCompl_mul_unif_zpow] at hv
  have hcast : ((r : F) - (r' : F)) = ((r - r' : 𝓞 F) : F) := by push_cast; ring
  rw [hcast] at hv

  by_contra hlt
  rw [not_lt] at hlt
  have : exp ((k v₀ : ℤ) + 1) ≤ exp (k v₀ : ℤ) :=
    le_trans (by simpa using mul_le_mul' hlt (le_refl (exp ((k v₀ : ℤ) + 1)))) hv
  rw [exp_le_exp] at this
  linarith

theorem relIndex_latt_latt_ne_zero (k k' : HOS →₀ ℕ) : (latt F k).relIndex (latt F k') ≠ 0 := fun h0 =>
  relIndex_latt_ne_zero F k' (AddSubgroup.relIndex_eq_zero_of_le_left (intLattice_le_latt F k) h0)

theorem absNorm_le_relIndex_step (k : HOS →₀ ℕ) (v₀ : HOS) :
    Ideal.absNorm v₀.asIdeal ≤ (latt F k).relIndex (latt F (k + Finsupp.single v₀ 1)) := by
  set L := latt F k
  set L' := latt F (k + Finsupp.single v₀ 1)
  have hLL' : L ≤ L' := latt_mono F le_self_add
  have hidx : (L.addSubgroupOf L').index = L.relIndex L' := rfl
  haveI : Finite (L' ⧸ L.addSubgroupOf L') := by
    apply Nat.finite_of_card_ne_zero
    rw [← AddSubgroup.index_eq_card, hidx]
    exact relIndex_latt_latt_ne_zero F _ _

  let ψ : 𝓞 F ⧸ v₀.asIdeal → L' ⧸ L.addSubgroupOf L' := fun c =>
    QuotientAddGroup.mk ⟨stepElt F k v₀ c.out, stepElt_mem F k v₀ _⟩
  have hψ : Function.Injective ψ := by
    intro c c' hcc'
    have hmem : -(⟨stepElt F k v₀ c.out, stepElt_mem F k v₀ _⟩ : L') + ⟨stepElt F k v₀ c'.out, stepElt_mem F k v₀ _⟩ ∈ L.addSubgroupOf L' :=
      QuotientAddGroup.eq.mp hcc'
    rw [AddSubgroup.mem_addSubgroupOf] at hmem
    have hmem' : stepElt F k v₀ c'.out - stepElt F k v₀ c.out ∈ L := by
      simp only [AddSubgroup.coe_add, AddSubgroup.coe_neg, neg_add_eq_sub] at hmem
      exact hmem
    have := sub_mem_asIdeal_of_stepElt_sub_mem F k v₀ hmem'
    rw [← Ideal.Quotient.mk_eq_mk_iff_sub_mem] at this
    rw [← Ideal.Quotient.mk_out c', ← Ideal.Quotient.mk_out c]
    exact this.symm
  calc Ideal.absNorm v₀.asIdeal = Nat.card (𝓞 F ⧸ v₀.asIdeal) := by rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
    _ ≤ Nat.card (L' ⧸ L.addSubgroupOf L') := Nat.card_le_card_of_injective ψ hψ
    _ = L.relIndex L' := by rw [← AddSubgroup.index_eq_card, hidx]

theorem absNorm_pow_le_relIndex (k : HOS →₀ ℕ) (v₀ : HOS) (n : ℕ) :
    Ideal.absNorm v₀.asIdeal ^ n ≤ (latt F k).relIndex (latt F (k + Finsupp.single v₀ n)) := by
  induction n with
  | zero => simp [AddSubgroup.relIndex_self]
  | succ n ih =>
    rw [pow_succ, Finsupp.single_add, ← add_assoc,
      ← AddSubgroup.relIndex_mul_relIndex (hHK := latt_mono F (le_self_add : k ≤ k + Finsupp.single v₀ n))
        (hKL := latt_mono F (le_self_add : k + Finsupp.single v₀ n ≤ k + Finsupp.single v₀ n + Finsupp.single v₀ 1))]
    exact Nat.mul_le_mul ih (absNorm_le_relIndex_step F _ v₀)

def normProd (k : HOS →₀ ℕ) : ℕ := k.prod fun v n => Ideal.absNorm v.asIdeal ^ n

theorem normProd_single_add {a : HOS} {b : ℕ} {f : HOS →₀ ℕ} (ha : a ∉ f.support) (hb : b ≠ 0) :
    normProd F (Finsupp.single a b + f) = Ideal.absNorm a.asIdeal ^ b * normProd F f := by
  have hsupp : (Finsupp.single a b + f).support = insert a f.support := by
    ext v
    simp only [Finsupp.mem_support_iff, Finsupp.add_apply, Finset.mem_insert, Finsupp.single_apply]
    by_cases hv : a = v
    · subst hv; simp [hb]
    · simp [hv, Ne.symm hv]
  have hva : ∀ v ∈ f.support, (Finsupp.single a b + f) v = f v := fun v hv => by
    have : a ≠ v := fun h => ha (h ▸ hv)
    rw [Finsupp.add_apply, Finsupp.single_eq_of_ne this.symm, zero_add]
  simp only [normProd, Finsupp.prod]
  rw [hsupp, Finset.prod_insert ha, Finsupp.add_apply, Finsupp.single_eq_same, Finsupp.notMem_support_iff.mp ha, add_zero]
  congr 1
  exact Finset.prod_congr rfl fun v hv => by rw [hva v hv]

theorem one_le_normProd (k : HOS →₀ ℕ) : 1 ≤ normProd F k := by
  rw [normProd, Finsupp.prod]
  exact Finset.one_le_prod' fun v _ => Nat.one_le_pow _ _ (Nat.pos_of_ne_zero (by
    rw [Ne, Ideal.absNorm_eq_zero_iff]; exact v.ne_bot))

theorem normProd_le_relIndex (k : HOS →₀ ℕ) : normProd F k ≤ (intLattice F).relIndex (latt F k) := by
  induction k using Finsupp.induction with
  | zero => exact Nat.one_le_iff_ne_zero.mpr (relIndex_latt_ne_zero F 0)
  | single_add a b f ha hb ih =>
    rw [normProd_single_add F ha hb, add_comm (Finsupp.single a b) f,
      ← AddSubgroup.relIndex_mul_relIndex (hHK := intLattice_le_latt F f) (hKL := latt_mono F (le_self_add : f ≤ f + Finsupp.single a b)),
      mul_comm]
    exact Nat.mul_le_mul ih (absNorm_pow_le_relIndex F f a b)

end R2
p2m_reactivate "P2MW.S_AutomorphicForm_weylIntertwiningIntegrand_finiteAdeleSlice_integrable_of_re_gt_half.AutomorphicForm P2MW.S_AutomorphicForm_weylIntertwiningIntegrand_finiteAdeleSlice_integrable_of_re_gt_half.AutomorphicForm.WeylIntegrable"

end AutomorphicForm.WeylIntegrable
p2m_reactivate "P2MW.S_AutomorphicForm_weylIntertwiningIntegrand_finiteAdeleSlice_integrable_of_re_gt_half.AutomorphicForm P2MW.S_AutomorphicForm_weylIntertwiningIntegrand_finiteAdeleSlice_integrable_of_re_gt_half.AutomorphicForm.WeylIntegrable"
p2m_reactivate "P2MW.S_AutomorphicForm_weylIntertwiningIntegrand_finiteAdeleSlice_integrable_of_re_gt_half.AutomorphicForm P2MW.S_AutomorphicForm_weylIntertwiningIntegrand_finiteAdeleSlice_integrable_of_re_gt_half.AutomorphicForm.WeylIntegrable"

end
p2m_reactivate "P2MW.S_AutomorphicForm_weylIntertwiningIntegrand_finiteAdeleSlice_integrable_of_re_gt_half.AutomorphicForm P2MW.S_AutomorphicForm_weylIntertwiningIntegrand_finiteAdeleSlice_integrable_of_re_gt_half.AutomorphicForm.WeylIntegrable"

noncomputable section

p2m_open "MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicBox IsDedekindDomain IsDedekindDomain.HeightOneSpectrum WithZero AutomorphicForm P2MW.S_AutomorphicForm_weylIntertwiningIntegrand_finiteAdeleSlice_integrable_of_re_gt_half.AutomorphicForm P2MW.S_AutomorphicForm_weylIntertwiningIntegrand_finiteAdeleSlice_integrable_of_re_gt_half.AutomorphicForm.WeylIntegrable"

open scoped ENNReal NNReal Pointwise Classical

namespace M4aP3C
namespace Rho7cSol

section FinSlice

variable (F : Type) [Field F] [NumberField F]

local notation "𝔸" => AdeleRing (𝓞 F) F
local notation "𝔸∞" => InfiniteAdeleRing F
local notation "𝔸f" => FiniteAdeleRing (𝓞 F) F
local notation "HOS" => HeightOneSpectrum (𝓞 F)

theorem fst_mul (x y : 𝔸) : (x * y).1 = x.1 * y.1 := rfl

theorem snd_mul (x y : 𝔸) : (x * y).2 = x.2 * y.2 := rfl

def finPart (Y : (𝔸)ˣ) : (𝔸f)ˣ where
  val := (Y : 𝔸).2
  inv := ((Y⁻¹ : (𝔸)ˣ) : 𝔸).2
  val_inv := by rw [← snd_mul, Units.mul_inv]; rfl
  inv_val := by rw [← snd_mul, Units.inv_mul]; rfl

def archPart (Y : (𝔸)ˣ) : (𝔸)ˣ where
  val := toAdele F (Y : 𝔸).1 1
  inv := toAdele F ((Y⁻¹ : (𝔸)ˣ) : 𝔸).1 1
  val_inv := Prod.ext (show (Y : 𝔸).1 * ((Y⁻¹ : (𝔸)ˣ) : 𝔸).1 = 1 by rw [← fst_mul, Units.mul_inv]; rfl) (one_mul 1)
  inv_val := Prod.ext (show ((Y⁻¹ : (𝔸)ˣ) : 𝔸).1 * (Y : 𝔸).1 = 1 by rw [← fst_mul, Units.inv_mul]; rfl) (one_mul 1)

theorem archPart_mul_finIdele (Y : (𝔸)ˣ) : archPart F Y * finIdele F (finPart F Y) = Y := by
  ext : 1
  show toAdele F (Y : 𝔸).1 1 * toAdele F 1 ((Y : 𝔸).2) = (Y : 𝔸)
  exact Prod.ext (mul_one _) (one_mul _)

theorem one_le_valued_selY_snd (a : 𝔸∞) (b : 𝔸f) (v : HOS) : 1 ≤ Valued.v ((selY F a b).2 v) := by
  rw [selY_snd]
  by_cases h : BigFin F b v
  · rw [if_pos h]; exact (one_lt_valued_of_bigFin F h).le
  · rw [if_neg h, map_one]

theorem valued_le_valued_selY_snd (a : 𝔸∞) (b : 𝔸f) (v : HOS) : Valued.v (b v) ≤ Valued.v ((selY F a b).2 v) := by
  rw [selY_snd]
  by_cases h : BigFin F b v
  · rw [if_pos h]
  · rw [if_neg h, map_one]
    exact (mem_adicCompletionIntegers _ _ _).mp (not_not.mp h)

theorem selY_fst_zero (t : 𝔸f) (w : InfinitePlace F) : (selY F 0 t).1 w = 1 := by
  rw [selY_fst, if_neg]
  intro h
  have h0 : (0 : 𝔸∞) w = 0 := rfl
  rw [BigInf, h0, norm_zero] at h
  exact (not_lt.mpr zero_le_one) h

theorem archPart_yUnit_zero (t : 𝔸f) : archPart F (yUnit (selRel F 0 t)) = 1 := by
  ext : 1
  show toAdele F (selY F 0 t).1 1 = (1 : 𝔸)
  exact Prod.ext (funext fun w => selY_fst_zero F t w) rfl

theorem mem_dilate_finPart (t : 𝔸f) : t ∈ dilate F (finPart F (yUnit (selRel F 0 t))) :=
  (mem_dilate_iff F _ _).mpr fun v => valued_le_valued_selY_snd F 0 t v

theorem distribHaarChar_yUnit_zero (t : 𝔸f) :
    (distribHaarChar 𝔸 (yUnit (selRel F 0 t)) : ℝ≥0∞) =
      (intLattice F).relIndex (dilate F (finPart F (yUnit (selRel F 0 t)))) := by
  have hv : ∀ v, 1 ≤ Valued.v (((finPart F (yUnit (selRel F 0 t)) : (𝔸f)ˣ) : 𝔸f) v) := fun v =>
    one_le_valued_selY_snd F 0 t v
  conv_lhs => rw [← archPart_mul_finIdele F (yUnit (selRel F 0 t)), map_mul, ENNReal.coe_mul, archPart_yUnit_zero F t,
    map_one, ENNReal.coe_one, one_mul]
  exact distribHaarChar_finIdele F (finPart F (yUnit (selRel F 0 t))) (intLattice_le_dilate F hv) (relIndex_dilate_ne_zero F _)

theorem measure_addSubgroup_eq_relIndex_mul [MeasurableSpace (FiniteAdeleRing (𝓞 F) F)] [BorelSpace (FiniteAdeleRing (𝓞 F) F)] (σ : Measure 𝔸f) [σ.IsAddLeftInvariant]
    (A B : AddSubgroup 𝔸f) (hAB : A ≤ B) (hA : IsClosed (A : Set 𝔸f)) (hfin : A.relIndex B ≠ 0) :
    σ B = A.relIndex B * σ A := by
  classical
  set H : AddSubgroup B := A.addSubgroupOf B with hH
  haveI : H.FiniteIndex := ⟨hfin⟩
  obtain ⟨s, hs, -⟩ := H.exists_isComplement_left 0
  haveI : Finite s := hs.finite_left_iff.mpr inferInstance
  have hcard : Nat.card s = A.relIndex B := hs.card_left
  have hcover : (B : Set 𝔸f) = ⋃ c : s, ((c : B) : 𝔸f) +ᵥ (A : Set 𝔸f) := by
    ext b
    simp only [Set.mem_iUnion, Set.mem_vadd_set, SetLike.mem_coe]
    constructor
    · intro hb
      have hmem : (⟨b, hb⟩ : B) ∈ (Set.univ : Set B) := Set.mem_univ _
      rw [← hs.add_eq] at hmem
      obtain ⟨c, hc, h, hh, hsum⟩ := Set.mem_add.mp hmem
      refine ⟨⟨c, hc⟩, (h : 𝔸f), ?_, ?_⟩
      · exact AddSubgroup.mem_addSubgroupOf.mp hh
      · exact congrArg Subtype.val hsum
    · rintro ⟨c, a, ha, rfl⟩
      exact B.add_mem (c : B).2 (hAB ha)
  have hdisj : Pairwise fun c c' : s => Disjoint (((c : B) : 𝔸f) +ᵥ (A : Set 𝔸f)) (((c' : B) : 𝔸f) +ᵥ (A : Set 𝔸f)) := by
    intro c c' hcc'
    have hd : Disjoint ((c : B) +ᵥ (H : Set B)) ((c' : B) +ᵥ (H : Set B)) :=
      hs.pairwiseDisjoint_vadd c.2 c'.2 (fun h => hcc' (Subtype.ext h))
    rw [Set.disjoint_iff_forall_ne]
    rintro _ ⟨a, ha, rfl⟩ _ ⟨a', ha', rfl⟩ heq
    have haB : a ∈ B := hAB ha
    have ha'B : a' ∈ B := hAB ha'
    refine hd.ne_of_mem (Set.mem_vadd_set.mpr ⟨⟨a, haB⟩, AddSubgroup.mem_addSubgroupOf.mpr ha, rfl⟩)
      (Set.mem_vadd_set.mpr ⟨⟨a', ha'B⟩, AddSubgroup.mem_addSubgroupOf.mpr ha', rfl⟩) ?_
    exact Subtype.ext heq
  have hmeasA : MeasurableSet (A : Set 𝔸f) := hA.measurableSet
  have hmeas : ∀ c : s, MeasurableSet (((c : B) : 𝔸f) +ᵥ (A : Set 𝔸f)) := fun c => hmeasA.const_vadd _
  have hconst : ∀ c : s, σ (((c : B) : 𝔸f) +ᵥ (A : Set 𝔸f)) = σ A := fun c => measure_vadd _ _ _
  rw [hcover, measure_iUnion hdisj hmeas, tsum_congr hconst]
  haveI := Fintype.ofFinite s
  rw [tsum_fintype, Finset.sum_const, Finset.card_univ, ← Nat.card_eq_fintype_card, hcard, nsmul_eq_mul]

theorem countable_ideal : Countable (Ideal (𝓞 F)) := by
  have h : (Set.univ : Set (Ideal (𝓞 F))) = ⋃ n : ℕ, {I : Ideal (𝓞 F) | Ideal.absNorm I = n} := by
    ext I; simp
  rw [← Set.countable_univ_iff, h]
  exact Set.countable_iUnion fun n => (Ideal.finite_setOf_absNorm_eq n).countable

scoped instance countable_heightOneSpectrum : Countable (HeightOneSpectrum (𝓞 F)) := by
  haveI := countable_ideal F
  exact Function.Injective.countable (f := fun v : HeightOneSpectrum (𝓞 F) => v.asIdeal) fun v w h => HeightOneSpectrum.ext h

scoped instance countable_finsupp_heightOneSpectrum : Countable (HeightOneSpectrum (𝓞 F) →₀ ℕ) := inferInstance

def idx (k : HOS →₀ ℕ) : ℝ≥0∞ := ((intLattice F).relIndex (latt F k) : ℝ≥0∞)

theorem idx_ne_zero (k : HOS →₀ ℕ) : idx F k ≠ 0 := by
  rw [idx, Ne, Nat.cast_eq_zero]; exact relIndex_latt_ne_zero F k

def domGf (a : ℝ) (t : 𝔸f) : ℝ≥0∞ :=
  ∑' k : HOS →₀ ℕ, idx F k ^ (-a) * (latt F k : Set 𝔸f).indicator 1 t

theorem measurableSet_latt [MeasurableSpace (FiniteAdeleRing (𝓞 F) F)] [BorelSpace (FiniteAdeleRing (𝓞 F) F)] (k : HOS →₀ ℕ) : MeasurableSet (latt F k : Set 𝔸f) :=
  (isCompact_latt F k).isClosed.measurableSet

theorem measurable_domGf_term [MeasurableSpace (FiniteAdeleRing (𝓞 F) F)] [BorelSpace (FiniteAdeleRing (𝓞 F) F)] (a : ℝ) (k : HOS →₀ ℕ) :
    Measurable fun t : 𝔸f => idx F k ^ (-a) * (latt F k : Set 𝔸f).indicator 1 t :=
  (measurable_one.indicator (measurableSet_latt F k)).const_mul _

theorem isClosed_intLattice : IsClosed (intLattice F : Set 𝔸f) := by
  rw [coe_intLattice]; exact isClosed_integralFiniteAdeles F

theorem lintegral_domGf [MeasurableSpace (FiniteAdeleRing (𝓞 F) F)] [BorelSpace (FiniteAdeleRing (𝓞 F) F)] (σ : Measure 𝔸f) [σ.IsAddLeftInvariant] (a : ℝ) :
    ∫⁻ t, domGf F a t ∂σ = (∑' k : HOS →₀ ℕ, idx F k ^ (1 - a)) * σ (integralFiniteAdeles (𝓞 F) F) := by
  simp only [domGf]
  rw [lintegral_tsum fun k => (measurable_domGf_term F a k).aemeasurable, ← ENNReal.tsum_mul_right]
  refine tsum_congr fun k => ?_
  rw [lintegral_const_mul _ (measurable_one.indicator (measurableSet_latt F k)),
    lintegral_indicator_one (measurableSet_latt F k),
    measure_addSubgroup_eq_relIndex_mul F σ (intLattice F) (latt F k) (intLattice_le_latt F k) (isClosed_intLattice F)
      (relIndex_latt_ne_zero F k),
    coe_intLattice, ← mul_assoc]
  congr 1
  rw [show (1 - a) = -a + 1 by ring, ENNReal.rpow_add _ _ (idx_ne_zero F k) (ENNReal.natCast_ne_top _), ENNReal.rpow_one, idx]

theorem tsum_idx_rpow_lt_top {a : ℝ} (ha : 2 < a) : ∑' k : HOS →₀ ℕ, idx F k ^ (1 - a) < ∞ := by
  have ht : 1 < a - 1 := by linarith
  have hfin : ∑' k : HOS →₀ ℕ, ((normProd F k : ℝ≥0∞) ^ (-(a - 1))) < ∞ :=
    NumberField.tsum_prod_absNorm_heightOneSpectrum_pow_rpow_neg_lt_top F ht
  refine lt_of_le_of_lt (ENNReal.tsum_le_tsum fun k => ?_) hfin
  rw [idx, show (1 - a) = -(a - 1) by ring, ENNReal.rpow_neg, ENNReal.rpow_neg]
  exact ENNReal.inv_le_inv.mpr (ENNReal.rpow_le_rpow (by exact_mod_cast normProd_le_relIndex F k) (by linarith))

theorem lintegral_domGf_lt_top [MeasurableSpace (FiniteAdeleRing (𝓞 F) F)] [BorelSpace (FiniteAdeleRing (𝓞 F) F)] (σ : Measure 𝔸f) [σ.IsAddLeftInvariant] [IsFiniteMeasureOnCompacts σ]
    {a : ℝ} (ha : 2 < a) : ∫⁻ t, domGf F a t ∂σ < ∞ := by
  rw [lintegral_domGf]
  exact ENNReal.mul_lt_top (tsum_idx_rpow_lt_top F ha) (isCompact_integralFiniteAdeles F).measure_lt_top

theorem ofReal_rpow_le_domGf (a : ℝ) (t : 𝔸f) :
    ENNReal.ofReal ((distribHaarChar 𝔸 (yUnit (selRel F 0 t)) : ℝ) ^ (-a)) ≤ domGf F a t := by
  have hv : ∀ v, 1 ≤ Valued.v (((finPart F (yUnit (selRel F 0 t)) : (𝔸f)ˣ) : 𝔸f) v) := fun v =>
    one_le_valued_selY_snd F 0 t v
  obtain ⟨k, hk, -⟩ := dilate_eq_latt F (finPart F (yUnit (selRel F 0 t))) hv
  have hmem : t ∈ (latt F k : Set 𝔸f) := by
    have h := mem_dilate_finPart F t
    rw [hk] at h
    exact h
  have hN : (distribHaarChar 𝔸 (yUnit (selRel F 0 t)) : ℝ≥0∞) = (((intLattice F).relIndex (latt F k) : ℕ) : ℝ≥0∞) := by
    rw [distribHaarChar_yUnit_zero F t, hk]
  have hNR : ((distribHaarChar 𝔸 (yUnit (selRel F 0 t)) : ℝ≥0) : ℝ) = ((intLattice F).relIndex (latt F k) : ℝ) := by
    have h2 : (distribHaarChar 𝔸 (yUnit (selRel F 0 t)) : ℝ≥0) = (((intLattice F).relIndex (latt F k) : ℕ) : ℝ≥0) := by
      exact_mod_cast hN
    rw [h2, NNReal.coe_natCast]
  have hNpos : (0 : ℝ) < ((intLattice F).relIndex (latt F k) : ℝ) :=
    Nat.cast_pos.mpr (Nat.pos_of_ne_zero (relIndex_latt_ne_zero F k))
  have hterm : idx F k ^ (-a) * (latt F k : Set 𝔸f).indicator 1 t =
      ENNReal.ofReal (((distribHaarChar 𝔸 (yUnit (selRel F 0 t)) : ℝ≥0) : ℝ) ^ (-a)) := by
    rw [Set.indicator_of_mem hmem, Pi.one_apply, mul_one, hNR, ← ENNReal.ofReal_rpow_of_pos hNpos,
      ENNReal.ofReal_natCast, idx]
  rw [← hterm]
  exact ENNReal.le_tsum k

theorem continuous_unipotentGL2_slice :
    Continuous (fun t : 𝔸f => (unipotentGL2 (toAdele F 0 t) : AdelicGL2 (𝓞 F) F)) := by
  have hval : Continuous (fun u : 𝔸 => ((unipotentGL2 u : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) 𝔸)) := by
    refine continuous_matrix fun i j => ?_
    simp only [unipotentGL2_coe]
    fin_cases i <;> fin_cases j <;> simp <;> fun_prop
  have hinv : ∀ u : 𝔸, ((unipotentGL2 u)⁻¹ : AdelicGL2 (𝓞 F) F) = unipotentGL2 (-u) := fun u =>
    inv_eq_of_mul_eq_one_right (by rw [← unipotentGL2_add, add_neg_cancel, unipotentGL2_zero])
  have hu : Continuous (fun u : 𝔸 => (unipotentGL2 u : AdelicGL2 (𝓞 F) F)) := by
    refine Units.continuous_iff.2 ⟨hval, ?_⟩
    simp_rw [hinv]
    exact hval.comp continuous_neg
  have hta : Continuous (fun t : 𝔸f => toAdele F 0 t) := continuous_const.prodMk continuous_id
  exact hu.comp hta

theorem adelicWeyl_inv : (adelicWeyl (𝓞 F) F)⁻¹ = adelicWeyl (𝓞 F) F := by
  rw [adelicWeyl, ← map_inv, gl2Weyl_inv]

theorem integrable_weylIntegrand_finSlice [MeasurableSpace (FiniteAdeleRing (𝓞 F) F)] [BorelSpace (FiniteAdeleRing (𝓞 F) F)] (σ : Measure 𝔸f) [σ.IsAddHaarMeasure]
    (α : (𝔸)ˣ →* ℝˣ) (hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ)) (hαΔ : ∀ x, ((α x : ℝˣ) : ℝ) = (distribHaarChar 𝔸 x : ℝ))
    (μc νc : (𝔸)ˣ →* ℂˣ) (hμ : IsUnitaryChar (𝓞 F) F μc) (hν : IsUnitaryChar (𝓞 F) F νc) (s : ℂ) (hs : 1 / 2 < s.re)
    (φ : AdelicGL2 (𝓞 F) F → ℂ) (hφ : IsInducedSection (𝓞 F) F (etaFst μc α hα s) (etaSnd νc α hα s) φ) (hφc : Continuous φ)
    (g : AdelicGL2 (𝓞 F) F) :
    Integrable (fun t : 𝔸f => φ (adelicWeyl (𝓞 F) F * unipotentGL2 (toAdele F 0 t) * g)) σ := by
  set a : ℝ := 2 * s.re + 1 with ha_def
  have ha2 : 2 < a := by rw [ha_def]; linarith

  have hcont : Continuous fun t : 𝔸f => φ (adelicWeyl (𝓞 F) F * unipotentGL2 (toAdele F 0 t) * g) :=
    hφc.comp ((continuous_const.mul (continuous_unipotentGL2_slice F)).mul continuous_const)
  refine ⟨hcont.aestronglyMeasurable, ?_⟩

  obtain ⟨B, hB0, hB⟩ := norm_apply_weyl_unipotent_le F α hα μc νc s φ hμ hν hφ hφc g
  have hpt : ∀ t : 𝔸f, ‖φ (adelicWeyl (𝓞 F) F * unipotentGL2 (toAdele F 0 t) * g)‖ₑ ≤
      ENNReal.ofReal B * domGf F a t := fun t => by
    rw [← ofReal_norm]
    have hBt := hB (toAdele F 0 t)
    rw [adelicWeyl_inv] at hBt
    refine (ENNReal.ofReal_le_ofReal hBt).trans ?_
    rw [ENNReal.ofReal_mul hB0, hαΔ]
    exact mul_le_mul' le_rfl (ofReal_rpow_le_domGf F a t)
  refine lt_of_le_of_lt (lintegral_mono hpt) ?_
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (lintegral_domGf_lt_top F σ ha2)

end FinSlice
p2m_reactivate "P2MW.S_AutomorphicForm_weylIntertwiningIntegrand_finiteAdeleSlice_integrable_of_re_gt_half.AutomorphicForm P2MW.S_AutomorphicForm_weylIntertwiningIntegrand_finiteAdeleSlice_integrable_of_re_gt_half.AutomorphicForm.WeylIntegrable"

end M4aP3C.Rho7cSol
p2m_reactivate "P2MW.S_AutomorphicForm_weylIntertwiningIntegrand_finiteAdeleSlice_integrable_of_re_gt_half.AutomorphicForm P2MW.S_AutomorphicForm_weylIntertwiningIntegrand_finiteAdeleSlice_integrable_of_re_gt_half.AutomorphicForm.WeylIntegrable P2MW.S_AutomorphicForm_weylIntertwiningIntegrand_finiteAdeleSlice_integrable_of_re_gt_half.M4aP3C P2MW.S_AutomorphicForm_weylIntertwiningIntegrand_finiteAdeleSlice_integrable_of_re_gt_half.M4aP3C.Rho7cSol"
p2m_reactivate "P2MW.S_AutomorphicForm_weylIntertwiningIntegrand_finiteAdeleSlice_integrable_of_re_gt_half.AutomorphicForm P2MW.S_AutomorphicForm_weylIntertwiningIntegrand_finiteAdeleSlice_integrable_of_re_gt_half.AutomorphicForm.WeylIntegrable P2MW.S_AutomorphicForm_weylIntertwiningIntegrand_finiteAdeleSlice_integrable_of_re_gt_half.M4aP3C"

end
p2m_reactivate "P2MW.S_AutomorphicForm_weylIntertwiningIntegrand_finiteAdeleSlice_integrable_of_re_gt_half.AutomorphicForm P2MW.S_AutomorphicForm_weylIntertwiningIntegrand_finiteAdeleSlice_integrable_of_re_gt_half.AutomorphicForm.WeylIntegrable P2MW.S_AutomorphicForm_weylIntertwiningIntegrand_finiteAdeleSlice_integrable_of_re_gt_half.M4aP3C P2MW.S_AutomorphicForm_weylIntertwiningIntegrand_finiteAdeleSlice_integrable_of_re_gt_half.M4aP3C.Rho7cSol"

open MeasureTheory NumberField IsDedekindDomain
p2m_open "AutomorphicForm P2MW.S_AutomorphicForm_weylIntertwiningIntegrand_finiteAdeleSlice_integrable_of_re_gt_half.AutomorphicForm"
open scoped NNReal

theorem solution
    (F : Type) [Field F] [NumberField F]
    [MeasurableSpace (FiniteAdeleRing (𝓞 F) F)]
    [BorelSpace (FiniteAdeleRing (𝓞 F) F)]
    (σ : Measure (FiniteAdeleRing (𝓞 F) F))
    [σ.IsAddHaarMeasure] :
    let α : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 F) F))).toHomUnits
    ∀ (hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ))
      (μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
      (_hμ : IsUnitaryChar (𝓞 F) F μ)
      (_hν : IsUnitaryChar (𝓞 F) F ν)
      (s : ℂ)
      (_hs : 1 / 2 < s.re)
      (φ : AdelicGL2 (𝓞 F) F → ℂ)
      (_hφ : IsInducedSection (𝓞 F) F (etaFst μ α hα s) (etaSnd ν α hα s) φ)
      (_hφc : Continuous φ)
      (g : AdelicGL2 (𝓞 F) F),
    Integrable (fun t : FiniteAdeleRing (𝓞 F) F =>
      φ (adelicWeyl (𝓞 F) F * unipotentGL2 (R := AdeleRing (𝓞 F) F) (0, t) * g)) σ := by
  intro α hα μ ν hμ hν s hs φ hφ hφc g
  exact M4aP3C.Rho7cSol.integrable_weylIntegrand_finSlice F σ α hα (fun x => rfl) μ ν hμ hν s hs φ hφ hφc g

#print axioms solution
#print axioms M4aP3C.Rho7cSol.integrable_weylIntegrand_finSlice
#print axioms M4aP3C.Rho7cSol.measure_addSubgroup_eq_relIndex_mul
#print axioms M4aP3C.Rho7cSol.distribHaarChar_yUnit_zero
#print axioms AutomorphicForm.WeylIntegrable.norm_apply_weyl_unipotent_le
#print axioms AutomorphicForm.WeylIntegrable.normProd_le_relIndex

end S_AutomorphicForm_weylIntertwiningIntegrand_finiteAdeleSlice_integrable_of_re_gt_half
end P2MW
export P2MW.S_AutomorphicForm_weylIntertwiningIntegrand_finiteAdeleSlice_integrable_of_re_gt_half (solution)
