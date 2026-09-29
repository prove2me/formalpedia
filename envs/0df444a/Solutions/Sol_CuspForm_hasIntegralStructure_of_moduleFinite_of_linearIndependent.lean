-- Prove2me | solution 1 for CuspForm.hasIntegralStructure_of_moduleFinite_of_linearIndependent
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/b7c10bfa-cfdc-50fd-8b46-7f0f4ceac08d

import Definitions.Def_CuspForm_IntegralStructure
import Definitions.Def_CuspForm_HeckeAlgebra
import Theorems.Thm_ModularFormClass_qCoeff_heckeT
import Theorems.Thm_ModularFormClass_qCoeff_heckeU
import Theorems.Thm_CuspForm_finiteDimensional_Gamma0
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CuspForm_hasIntegralStructure_of_moduleFinite_of_linearIndependent

set_option autoImplicit false

open Module CongruenceSubgroup ModularFormClass UpperHalfPlane

namespace QIntReduce

private theorem one_mem_strictPeriods_Gamma0 (N : ℕ) :
    (1 : ℝ) ∈ ((Gamma0 N : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ)) :
      Subgroup (Matrix.GeneralLinearGroup (Fin 2) ℝ)).strictPeriods := by
  rw [CongruenceSubgroup.strictPeriods_Gamma0]
  exact AddSubgroup.mem_zmultiples _

variable {N' : ℕ} {k : ℤ}

private theorem qCoeff_add (f g : CuspForm (Gamma0 N') k) (n : ℕ) :
    qCoeff (⇑(f + g)) n = qCoeff (⇑f) n + qCoeff (⇑g) n := by
  have hf := ModularFormClass.analyticAt_cuspFunction_zero f one_pos
    (one_mem_strictPeriods_Gamma0 N')
  have hg := ModularFormClass.analyticAt_cuspFunction_zero g one_pos
    (one_mem_strictPeriods_Gamma0 N')
  simp only [qCoeff, CuspForm.coe_add, qExpansion_add hf hg, map_add]

private theorem qCoeff_smul (c : ℂ) (f : CuspForm (Gamma0 N') k) (n : ℕ) :
    qCoeff (⇑(c • f)) n = c * qCoeff (⇑f) n := by
  have hf := ModularFormClass.analyticAt_cuspFunction_zero f one_pos
    (one_mem_strictPeriods_Gamma0 N')
  simp only [qCoeff, CuspForm.IsGLPos.coe_smul, qExpansion_smul hf c, PowerSeries.coeff_smul,
    smul_eq_mul]

private noncomputable def qCoeffL (N' : ℕ) (k : ℤ) (n : ℕ) : CuspForm (Gamma0 N') k →ₗ[ℂ] ℂ where
  toFun f := qCoeff (⇑f) n
  map_add' f g := qCoeff_add f g n
  map_smul' c f := by simpa using qCoeff_smul c f n

@[scoped simp] private theorem qCoeffL_apply (n : ℕ) (f : CuspForm (Gamma0 N') k) :
    qCoeffL N' k n f = qCoeff (⇑f) n := rfl

private theorem qCoeff_sub (f g : CuspForm (Gamma0 N') k) (n : ℕ) :
    qCoeff (⇑(f - g)) n = qCoeff (⇑f) n - qCoeff (⇑g) n := by
  rw [← qCoeffL_apply n, ← qCoeffL_apply n f, ← qCoeffL_apply n g, map_sub]

private theorem qCoeff_heckeTLin {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N')
    (f : CuspForm (Gamma0 N') k) (m : ℕ) :
    qCoeff (⇑(CuspForm.heckeTLin k hℓ hℓN f)) m =
      qCoeff (⇑f) (m * ℓ) + if ℓ ∣ m then (ℓ : ℂ) ^ (k - 1) * qCoeff (⇑f) (m / ℓ) else 0 := by
  rw [CuspForm.coe_heckeTLin_apply, ModularFormClass.qCoeff_heckeT f
    (one_mem_strictPeriods_Gamma0 N') hℓ.ne_zero m, ModularForm.coeffHeckeT_apply]

private theorem qCoeff_heckeULin [NeZero N'] {q : ℕ} (hq : q.Prime) (hqN : q ∣ N')
    (f : CuspForm (Gamma0 N') k) (m : ℕ) :
    qCoeff (⇑(CuspForm.heckeULin k hqN f)) m = qCoeff (⇑f) (m * q) := by
  rw [CuspForm.coe_heckeULin_apply, ModularFormClass.qCoeff_heckeU f
    (one_mem_strictPeriods_Gamma0 N') hq.ne_zero m, ModularForm.coeffHeckeU_apply]

private theorem exists_heckeOp (N' : ℕ) [NeZero N'] (k : ℤ) (hk : 1 ≤ k) (n : ℕ) (hn : 0 < n) :
    ∃ t ∈ CuspForm.heckeAlgebra N' k (∅ : Set ℕ),
      ∀ f : CuspForm (Gamma0 N') k, qCoeff (⇑(t f)) 1 = qCoeff (⇑f) n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  rcases eq_or_ne n 1 with rfl | hn1
  · exact ⟨1, Subalgebra.one_mem _, fun f => rfl⟩
  obtain ⟨ℓ, hℓ, m, rfl⟩ := Nat.exists_prime_and_dvd hn1
  have hm : 0 < m := Nat.pos_of_ne_zero (by rintro rfl; simp at hn)
  have hmn : m < ℓ * m := lt_mul_left hm hℓ.one_lt
  obtain ⟨tm, htm, htm'⟩ := ih m hmn hm
  by_cases hℓN : ℓ ∣ N'
  · refine ⟨tm * CuspForm.heckeULin k hℓN,
      mul_mem htm (CuspForm.heckeULin_mem_heckeAlgebra hℓ hℓN (by simp)), fun f => ?_⟩
    rw [Module.End.mul_apply, htm', qCoeff_heckeULin hℓ hℓN, mul_comm]
  · by_cases hℓm : ℓ ∣ m
    · obtain ⟨r, hr⟩ := hℓm
      have hr0 : 0 < r := Nat.pos_of_ne_zero (by rintro rfl; simp [hr] at hm)
      have hrm : r ≤ m := by rw [hr]; exact Nat.le_mul_of_pos_left r hℓ.pos
      obtain ⟨tr, htr, htr'⟩ := ih r (lt_of_le_of_lt hrm hmn) hr0
      have hcast : (((ℓ ^ (k - 1).toNat : ℕ) : ℤ) : ℂ) = (ℓ : ℂ) ^ (k - 1) := by
        push_cast
        rw [← zpow_natCast, Int.toNat_of_nonneg (by omega : (0 : ℤ) ≤ k - 1)]
      refine ⟨tm * CuspForm.heckeTLin k hℓ hℓN - ((ℓ ^ (k - 1).toNat : ℕ) : ℤ) • tr,
        sub_mem (mul_mem htm (CuspForm.heckeTLin_mem_heckeAlgebra hℓ hℓN (by simp)))
          (Subalgebra.smul_mem _ htr _), fun f => ?_⟩
      have hdiv : m / ℓ = r := by rw [hr, Nat.mul_div_cancel_left r hℓ.pos]
      have hsmul : qCoeff (⇑(((((ℓ ^ (k - 1).toNat : ℕ) : ℤ) • tr) f))) 1 =
          (ℓ : ℂ) ^ (k - 1) * qCoeff (⇑f) r := by
        rw [LinearMap.smul_apply, ← Int.cast_smul_eq_zsmul ℂ, qCoeff_smul, htr', hcast]
      rw [LinearMap.sub_apply, qCoeff_sub, Module.End.mul_apply, htm',
        qCoeff_heckeTLin hℓ hℓN, if_pos ⟨r, hr⟩, hdiv, hsmul, mul_comm m ℓ]
      ring
    · refine ⟨tm * CuspForm.heckeTLin k hℓ hℓN,
        mul_mem htm (CuspForm.heckeTLin_mem_heckeAlgebra hℓ hℓN (by simp)), fun f => ?_⟩
      rw [Module.End.mul_apply, htm', qCoeff_heckeTLin hℓ hℓN, if_neg hℓm, add_zero, mul_comm]

end QIntReduce
p2m_reactivate "P2MW.S_CuspForm_hasIntegralStructure_of_moduleFinite_of_linearIndependent.QIntReduce"

namespace QIntReduce

variable {K W : Type} [Field K] [AddCommGroup W] [Module K W]

private def pairEnd (e : W →ₗ[K] K) : Module.End K W →ₗ[K] Module.Dual K W :=
  LinearMap.llcomp K W W K e

@[scoped simp] private theorem pairEnd_apply (e : W →ₗ[K] K) (T : Module.End K W) (w : W) :
    pairEnd e T w = e (T w) := rfl

private def pairVec (G : Set (Module.End K W)) (e : W →ₗ[K] K) :
    W →ₗ[K] Module.Dual K ↥(Submodule.span K G) :=
  ((pairEnd e).domRestrict (Submodule.span K G)).flip

@[scoped simp] private theorem pairVec_apply (G : Set (Module.End K W)) (e : W →ₗ[K] K) (w : W)
    (T : ↥(Submodule.span K G)) :
    pairVec G e w T = e ((T : Module.End K W) w) := rfl

private theorem commute_span (G : Set (Module.End K W)) (g : Module.End K W)
    (hg : ∀ g' ∈ G, Commute g g') (T : Module.End K W) (hT : T ∈ Submodule.span K G) :
    Commute g T := by
  induction hT using Submodule.span_induction with
  | mem x hx => exact hg x hx
  | zero => exact Commute.zero_right g
  | add x y hx hy ihx ihy => exact ihx.add_right ihy
  | smul c x hx ih => exact ih.smul_right c

private theorem end_eq_zero_of_forall_pair_eq_zero (G : Set (Module.End K W)) (e : W →ₗ[K] K)
    (hcomm : ∀ g ∈ G, ∀ g' ∈ G, Commute g g')
    (hright : ∀ w : W, (∀ g ∈ G, e (g w) = 0) → w = 0)
    (T : Module.End K W) (hT : T ∈ Submodule.span K G)
    (h : ∀ w : W, e (T w) = 0) : T = 0 := by
  ext w
  show T w = 0
  refine hright (T w) fun g hg => ?_
  have hgT : Commute g T := commute_span G g (fun g' hg' => hcomm g hg g' hg') T hT
  have hswap : g (T w) = T (g w) := by
    calc g (T w) = (g * T) w := rfl
    _ = (T * g) w := by rw [hgT.eq]
    _ = T (g w) := rfl
  rw [hswap]
  exact h (g w)

private theorem pairVec_injective (G : Set (Module.End K W)) (e : W →ₗ[K] K)
    (hright : ∀ w : W, (∀ g ∈ G, e (g w) = 0) → w = 0) :
    Function.Injective (pairVec G e) := by
  rw [injective_iff_map_eq_zero]
  intro w hw
  refine hright w fun g hg => ?_
  have := congrArg (fun φ => φ ⟨g, Submodule.subset_span hg⟩) hw
  simpa using this

variable [FiniteDimensional K W]

private theorem finrank_le_finrank_span (G : Set (Module.End K W)) (e : W →ₗ[K] K)
    (hright : ∀ w : W, (∀ g ∈ G, e (g w) = 0) → w = 0) :
    Module.finrank K W ≤ Module.finrank K ↥(Submodule.span K G) := by
  have h1 := LinearMap.finrank_le_finrank_of_injective (pairVec_injective G e hright)
  rwa [Subspace.dual_finrank_eq] at h1

private theorem finrank_span_le (G : Set (Module.End K W)) (e : W →ₗ[K] K)
    (hcomm : ∀ g ∈ G, ∀ g' ∈ G, Commute g g')
    (hright : ∀ w : W, (∀ g ∈ G, e (g w) = 0) → w = 0) :
    Module.finrank K ↥(Submodule.span K G) ≤ Module.finrank K W := by
  have hinj : Function.Injective ((pairEnd e).domRestrict (Submodule.span K G)) := by
    rw [injective_iff_map_eq_zero]
    rintro ⟨T, hT⟩ h0
    refine Subtype.ext (end_eq_zero_of_forall_pair_eq_zero G e hcomm hright T hT fun w => ?_)
    have := congrArg (fun φ => φ w) h0
    simpa using this
  have h2 := LinearMap.finrank_le_finrank_of_injective hinj
  rwa [Subspace.dual_finrank_eq] at h2

private theorem finrank_span_pair_eq (G : Set (Module.End K W)) (e : W →ₗ[K] K)
    (hcomm : ∀ g ∈ G, ∀ g' ∈ G, Commute g g')
    (hright : ∀ w : W, (∀ g ∈ G, e (g w) = 0) → w = 0) :
    Module.finrank K ↥(Submodule.span K G) = Module.finrank K W :=
  le_antisymm (finrank_span_le G e hcomm hright) (finrank_le_finrank_span G e hright)

private theorem exists_vec_of_functional (G : Set (Module.End K W)) (e : W →ₗ[K] K)
    (hcomm : ∀ g ∈ G, ∀ g' ∈ G, Commute g g')
    (hright : ∀ w : W, (∀ g ∈ G, e (g w) = 0) → w = 0)
    (φ : Module.End K W →ₗ[K] K) :
    ∃ w : W, ∀ T ∈ Submodule.span K G, φ T = e (T w) := by
  have hdim : Module.finrank K W = Module.finrank K (Module.Dual K ↥(Submodule.span K G)) := by
    rw [Subspace.dual_finrank_eq, finrank_span_pair_eq G e hcomm hright]
  have hsurj : Function.Surjective (pairVec G e) :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp
      (pairVec_injective G e hright)
  obtain ⟨w, hw⟩ := hsurj (φ.domRestrict (Submodule.span K G))
  refine ⟨w, fun T hT => ?_⟩
  have := congrArg (fun ψ => ψ ⟨T, hT⟩) hw
  simpa using this.symm

end QIntReduce
p2m_reactivate "P2MW.S_CuspForm_hasIntegralStructure_of_moduleFinite_of_linearIndependent.QIntReduce"

namespace QIntReduce

variable {N' : ℕ} {k : ℤ}

private theorem cuspForm_eq_zero_of_forall_qCoeff_eq_zero [NeZero N']
    (f : CuspForm (Gamma0 N') k) (h0 : ∀ n : ℕ, qCoeff (⇑f) n = 0) : f = 0 := by
  have hΓ := one_mem_strictPeriods_Gamma0 N'
  have hqe : qExpansion 1 (⇑f) = 0 := by
    ext n
    simpa [qCoeff] using h0 n
  have hf0 : (⇑f : ℍ → ℂ) = 0 :=
    (qExpansion_eq_zero_iff one_pos (SlashInvariantFormClass.periodic_comp_ofComplex f hΓ)
      (holo f) (bdd_at_infty f)).mp hqe
  ext τ
  simpa using congrFun hf0 τ

private theorem heckeAlgebra_commute (N' : ℕ) [NeZero N'] (k : ℤ) :
    ∀ g ∈ (CuspForm.heckeAlgebra N' k (∅ : Set ℕ) :
        Set (Module.End ℂ (CuspForm (Gamma0 N') k))),
      ∀ g' ∈ (CuspForm.heckeAlgebra N' k (∅ : Set ℕ) :
        Set (Module.End ℂ (CuspForm (Gamma0 N') k))), Commute g g' := by
  intro g hg g' hg'
  have h := mul_comm (⟨g, hg⟩ : CuspForm.heckeAlgebra N' k (∅ : Set ℕ)) ⟨g', hg'⟩
  have h2 := congrArg Subtype.val h
  simp at h2
  exact h2

private theorem heckeAlgebra_pair_right_nondeg (N' : ℕ) [NeZero N'] (k : ℤ) (hk : 1 ≤ k) :
    ∀ f : CuspForm (Gamma0 N') k,
      (∀ g ∈ (CuspForm.heckeAlgebra N' k (∅ : Set ℕ) :
          Set (Module.End ℂ (CuspForm (Gamma0 N') k))),
        qCoeffL N' k 1 (g f) = 0) → f = 0 := by
  intro f hf
  refine cuspForm_eq_zero_of_forall_qCoeff_eq_zero f fun n => ?_
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simpa [qCoeff] using
      CuspFormClass.qExpansion_coeff_zero f one_pos (one_mem_strictPeriods_Gamma0 N')
  · obtain ⟨t, ht, ht'⟩ := exists_heckeOp N' k hk n hn
    have h1 := hf t ht
    rw [qCoeffL_apply, ht' f] at h1
    exact h1

private theorem finrank_span_heckeAlgebra_eq_finrank (N' : ℕ) [NeZero N'] (k : ℤ) (hk : 1 ≤ k) :
    Module.finrank ℂ (Submodule.span ℂ (CuspForm.heckeAlgebra N' k (∅ : Set ℕ) :
      Set (Module.End ℂ (CuspForm (Gamma0 N') k)))) =
      Module.finrank ℂ (CuspForm (Gamma0 N') k) := by
  haveI := CuspForm.finiteDimensional_Gamma0 N' k
  exact finrank_span_pair_eq _ (qCoeffL N' k 1) (heckeAlgebra_commute N' k)
    (heckeAlgebra_pair_right_nondeg N' k hk)

private theorem exists_form_of_functional_span_heckeAlgebra (N' : ℕ) [NeZero N'] (k : ℤ) (hk : 1 ≤ k)
    (φ : Module.End ℂ (CuspForm (Gamma0 N') k) →ₗ[ℂ] ℂ) :
    ∃ f : CuspForm (Gamma0 N') k,
      ∀ T ∈ Submodule.span ℂ (CuspForm.heckeAlgebra N' k (∅ : Set ℕ) :
        Set (Module.End ℂ (CuspForm (Gamma0 N') k))), φ T = qCoeff (⇑(T f)) 1 := by
  haveI := CuspForm.finiteDimensional_Gamma0 N' k
  obtain ⟨f, hf⟩ := exists_vec_of_functional _ (qCoeffL N' k 1) (heckeAlgebra_commute N' k)
    (heckeAlgebra_pair_right_nondeg N' k hk) φ
  exact ⟨f, fun T hT => by simpa using hf T hT⟩

end QIntReduce
p2m_reactivate "P2MW.S_CuspForm_hasIntegralStructure_of_moduleFinite_of_linearIndependent.QIntReduce"

namespace QIntReduce

variable {N' : ℕ} {k : ℤ}

private theorem sum_ite_coord {ι : Type} [Fintype ι] [DecidableEq ι] (j : ι) (c : ι → ℂ) :
    (∑ i, if i = j then c i else 0) = c j := by
  rw [Finset.sum_ite_eq' Finset.univ j c, if_pos (Finset.mem_univ j)]

set_option maxHeartbeats 1600000 in

private theorem hasIntegralStructure_of_hyps_core (N' : ℕ) [NeZero N'] (k : ℤ)
    (hMF : Module.Finite ℤ (CuspForm.heckeAlgebra N' k (∅ : Set ℕ)))
    (hext : ∀ n : ℕ, 0 < n → ∃ t ∈ CuspForm.heckeAlgebra N' k (∅ : Set ℕ),
      ∀ f : CuspForm (Gamma0 N') k, qCoeff (⇑(t f)) 1 = qCoeff (⇑f) n)
    (hfr : Module.finrank ℂ (Submodule.span ℂ (CuspForm.heckeAlgebra N' k (∅ : Set ℕ) :
        Set (Module.End ℂ (CuspForm (Gamma0 N') k)))) =
      Module.finrank ℂ (CuspForm (Gamma0 N') k))
    (hexf : ∀ φ : Module.End ℂ (CuspForm (Gamma0 N') k) →ₗ[ℂ] ℂ,
      ∃ f : CuspForm (Gamma0 N') k,
        ∀ T ∈ Submodule.span ℂ (CuspForm.heckeAlgebra N' k (∅ : Set ℕ) :
          Set (Module.End ℂ (CuspForm (Gamma0 N') k))), φ T = qCoeff (⇑(T f)) 1)
    (hdesc : ∀ {ι : Type} (t : ι → CuspForm.heckeAlgebra N' k (∅ : Set ℕ)),
      LinearIndependent ℤ t →
      LinearIndependent ℂ fun i => ((t i : CuspForm.heckeAlgebra N' k (∅ : Set ℕ)) :
        Module.End ℂ (CuspForm (Gamma0 N') k))) :
    CuspForm.HasIntegralStructure N' k := by
  classical
  haveI := CuspForm.finiteDimensional_Gamma0 N' k
  haveI := hMF
  haveI : Module.Free ℤ (CuspForm.heckeAlgebra N' k (∅ : Set ℕ)) :=
    Module.free_of_finite_type_torsion_free'
  let b : Basis (Module.Free.ChooseBasisIndex ℤ (CuspForm.heckeAlgebra N' k (∅ : Set ℕ))) ℤ
      (CuspForm.heckeAlgebra N' k (∅ : Set ℕ)) :=
    Module.Free.chooseBasis ℤ (CuspForm.heckeAlgebra N' k (∅ : Set ℕ))
  set ι := Module.Free.ChooseBasisIndex ℤ (CuspForm.heckeAlgebra N' k (∅ : Set ℕ)) with hι

  set u : ι → Module.End ℂ (CuspForm (Gamma0 N') k) :=
    fun i => ((b i : CuspForm.heckeAlgebra N' k (∅ : Set ℕ)) :
      Module.End ℂ (CuspForm (Gamma0 N') k)) with hu_def
  have hu : LinearIndependent ℂ u := hdesc b b.linearIndependent

  have hval : ∀ (T : Module.End ℂ (CuspForm (Gamma0 N') k)) (hT : T ∈ CuspForm.heckeAlgebra N' k
      (∅ : Set ℕ)), T = ∑ i, ((b.repr ⟨T, hT⟩ i : ℤ) : ℂ) • u i := by
    intro T hT
    have h0 := congrArg Subtype.val (b.sum_repr ⟨T, hT⟩)
    refine h0.symm.trans ?_
    rw [AddSubmonoidClass.coe_finsetSum]
    exact Finset.sum_congr rfl fun i _ => by rw [SetLike.val_smul, Int.cast_smul_eq_zsmul]

  have hsp : Submodule.span ℂ (Set.range u) =
      Submodule.span ℂ (CuspForm.heckeAlgebra N' k (∅ : Set ℕ) :
        Set (Module.End ℂ (CuspForm (Gamma0 N') k))) := by
    refine le_antisymm (Submodule.span_le.mpr ?_) (Submodule.span_le.mpr ?_)
    · rintro _ ⟨i, rfl⟩
      exact Submodule.subset_span (b i).2
    · intro T hT
      rw [hval T hT]
      exact Submodule.sum_mem _ fun i _ =>
        Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

  have hcard : Fintype.card ι = Module.finrank ℂ (CuspForm (Gamma0 N') k) := by
    have h1 : Module.finrank ℂ (Submodule.span ℂ (Set.range u)) = Fintype.card ι :=
      finrank_span_eq_card hu
    have h2 := (LinearEquiv.ofEq _ _ hsp).finrank_eq
    exact (h1.symm.trans h2).trans hfr

  let Bsp : Basis ι ℂ (Submodule.span ℂ (CuspForm.heckeAlgebra N' k (∅ : Set ℕ) :
      Set (Module.End ℂ (CuspForm (Gamma0 N') k)))) :=
    (Basis.span hu).map (LinearEquiv.ofEq _ _ hsp)
  choose Ψ hΨ using fun j : ι => LinearMap.exists_extend (Bsp.coord j)
  choose F hF using fun j : ι => hexf (Ψ j)

  have hcoord : ∀ (T : Module.End ℂ (CuspForm (Gamma0 N') k))
      (hT : T ∈ CuspForm.heckeAlgebra N' k (∅ : Set ℕ)) (j : ι),
      Ψ j T = ((b.repr ⟨T, hT⟩ j : ℤ) : ℂ) := by
    intro T hT j
    have h1 : Ψ j T = Bsp.coord j ⟨T, Submodule.subset_span hT⟩ := by
      have := congrArg (fun ψ => ψ ⟨T, Submodule.subset_span hT⟩) (hΨ j)
      simpa using this
    rw [h1]
    have helt : (⟨T, Submodule.subset_span hT⟩ :
        Submodule.span ℂ (CuspForm.heckeAlgebra N' k (∅ : Set ℕ) :
          Set (Module.End ℂ (CuspForm (Gamma0 N') k)))) =
        ∑ i, ((b.repr ⟨T, hT⟩ i : ℤ) : ℂ) • Bsp i := by
      apply Subtype.ext
      push_cast [Submodule.coe_sum, SetLike.val_smul]
      conv_lhs => rw [hval T hT]
      exact Finset.sum_congr rfl fun i _ => by
        congr 1
        simp [Bsp, Basis.map_apply, LinearEquiv.coe_ofEq_apply, Basis.span_apply]
    rw [helt, map_sum]
    simp only [map_smul, Basis.coord_apply, Basis.repr_self,
      Finsupp.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]
    exact sum_ite_coord j fun i => ((b.repr ⟨T, hT⟩ i : ℤ) : ℂ)

  have hFmem : ∀ j, F j ∈ CuspForm.intLattice N' k := by
    intro j
    unfold CuspForm.intLattice
    refine Submodule.subset_span ?_
    simp only [Set.mem_setOf_eq]
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · refine ⟨0, ?_⟩
      rw [Int.cast_zero]
      simpa [qCoeff] using
        CuspFormClass.qExpansion_coeff_zero (F j) one_pos (one_mem_strictPeriods_Gamma0 N')
    · obtain ⟨t, ht, ht'⟩ := hext n hn
      refine ⟨b.repr ⟨t, ht⟩ j, ?_⟩
      rw [← ht' (F j), ← hF j t (Submodule.subset_span ht), hcoord t ht j]

  have hFind : LinearIndependent ℂ F := by
    rw [linearIndependent_iff']
    intro s c hsum j hj
    have hterm : ∀ i, qCoeffL N' k 1
        (((Bsp j : Submodule.span ℂ (CuspForm.heckeAlgebra N' k (∅ : Set ℕ) :
          Set (Module.End ℂ (CuspForm (Gamma0 N') k)))) :
            Module.End ℂ (CuspForm (Gamma0 N') k)) (F i)) = if j = i then 1 else 0 := by
      intro i
      rw [qCoeffL_apply, ← hF i _ (Bsp j).2]
      have h1 := congrArg (fun ψ => ψ (Bsp j)) (hΨ i)
      simp only [LinearMap.comp_apply, Submodule.subtype_apply] at h1
      rw [h1]
      simp [Basis.coord_apply, Basis.repr_self, Finsupp.single_apply]
    have key := congrArg (fun g => qCoeffL N' k 1
      (((Bsp j : Submodule.span ℂ (CuspForm.heckeAlgebra N' k (∅ : Set ℕ) :
        Set (Module.End ℂ (CuspForm (Gamma0 N') k)))) :
          Module.End ℂ (CuspForm (Gamma0 N') k)) g)) hsum
    simp only [map_sum, map_smul, smul_eq_mul, map_zero] at key
    simpa [hterm, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, hj] using key

  have hspanF : Submodule.span ℂ (Set.range F) = ⊤ :=
    hFind.span_eq_top_of_card_eq_finrank' hcard
  unfold CuspForm.HasIntegralStructure
  rw [eq_top_iff, ← hspanF]
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨j, rfl⟩
  exact Submodule.subset_span (hFmem j)

end QIntReduce
p2m_reactivate "P2MW.S_CuspForm_hasIntegralStructure_of_moduleFinite_of_linearIndependent.QIntReduce"

theorem solution (N : ℕ) [NeZero N] (k : ℤ) (hk : 1 ≤ k)
    (hfin : Module.Finite ℤ (CuspForm.heckeAlgebra N k (∅ : Set ℕ)))
    (hind : ∀ {ι : Type} (T : ι → CuspForm.heckeAlgebra N k (∅ : Set ℕ)), LinearIndependent ℤ T →
      LinearIndependent ℂ
        (fun i => ((T i : CuspForm.heckeAlgebra N k (∅ : Set ℕ)) :
          Module.End ℂ (CuspForm (CongruenceSubgroup.Gamma0 N) k)))) :
    CuspForm.HasIntegralStructure N k :=
  QIntReduce.hasIntegralStructure_of_hyps_core N k hfin
    (fun n hn => QIntReduce.exists_heckeOp N k hk n hn)
    (QIntReduce.finrank_span_heckeAlgebra_eq_finrank N k hk)
    (QIntReduce.exists_form_of_functional_span_heckeAlgebra N k hk)
    hind

end S_CuspForm_hasIntegralStructure_of_moduleFinite_of_linearIndependent
end P2MW
export P2MW.S_CuspForm_hasIntegralStructure_of_moduleFinite_of_linearIndependent (solution)
