-- Prove2me | solution 1 for DihedralWeightOne.qCoeff_hecke_eq_of_hasNebentypus_of_sum_weightOneLift_mul_padicToAdelic_inv_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/33522634-1f7d-59ed-b0ba-1662b4c79972

import Mathlib
import Definitions.Def_AutomorphicForm_DihedralWeightOneLift
import Definitions.Def_CuspForm_PrimitiveFormGamma1
import Definitions.Def_LocalNewvector_AdelicSpanCarrier
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_ModularForm_HeckeOperator
import Definitions.Def_LocalNewvector_CongruenceSubgroupK1
import Theorems.Thm_ModularFormClass_qCoeff_heckeU
import Theorems.Thm_CuspForm_exists_degeneracy_gamma1_hasNebentypus
import Theorems.Thm_DihedralWeightOne_weightOneLift_globalPoints_mul_and_mul_finEmbed_and_eq_weightOneArchLift
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_DihedralWeightOne_qCoeff_hecke_eq_of_hasNebentypus_of_sum_weightOneLift_mul_padicToAdelic_inv_eq
p2m_attr_erase "simp" "FreyPackage.ModMCarrier.coe_rescaleLin_apply ModularForm.AtkinLehnerDatum.mk.injEq ModularForm.AtkinLehnerDatum.alGL_coe ModularForm.AtkinLehnerDatum.mk.sizeOf_spec ModularForm.AtkinLehnerDatum.sqUnitSL_coe ModularForm.AtkinLehnerDatum.det_sqUnit ModularForm.AtkinLehnerDatum.det_mat"

set_option autoImplicit false

open NumberField NumberField.AdelicLevel AutomorphicForm DihedralWeightOne IsDedekindDomain
open scoped MatrixGroups ModularForm

set_option autoImplicit false

open NumberField AdelicDock IsDedekindDomain

namespace HeckeCosets

variable (p : ℕ) [hp : Fact p.Prime]

private noncomputable def repZ (i : Fin (p + 1)) : Matrix (Fin 2) (Fin 2) ℤ_[p] :=
  if (i : ℕ) < p then !![1, ((i : ℕ) : ℤ_[p]); 0, (p : ℤ_[p])] else !![(p : ℤ_[p]), 0; 0, 1]

private theorem repZ_of_lt {i : Fin (p + 1)} (hi : (i : ℕ) < p) :
    repZ p i = !![1, ((i : ℕ) : ℤ_[p]); 0, (p : ℤ_[p])] := by
  simp [repZ, hi]

private theorem repZ_last : repZ p (Fin.last p) = !![(p : ℤ_[p]), 0; 0, 1] := by
  simp [repZ]

private theorem det_repZ (i : Fin (p + 1)) : (repZ p i).det = (p : ℤ_[p]) := by
  unfold repZ
  split_ifs <;> simp [Matrix.det_fin_two_of]

end HeckeCosets

namespace DescentSupportA

private theorem coe_finComponent {R : Type*} [CommRing R] [IsDedekindDomain R]
    {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
    (w : HeightOneSpectrum R) (g : GL (Fin 2) (FiniteAdeleRing R K)) :
    ((AdelicLevel.finComponent R K w g) : Matrix (Fin 2) (Fin 2) (w.adicCompletion K))
      = (AdelicLevel.finAdeleEval R K w).mapMatrix
          (g : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K)) := by
  ext i j
  rw [AdelicLevel.finComponent_apply, RingHom.mapMatrix_apply, Matrix.map_apply,
    AdelicLevel.finAdeleEval_apply]

private theorem glEq_of_forall_finComponent_eq {R : Type*} [CommRing R] [IsDedekindDomain R]
    {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
    {g h : GL (Fin 2) (FiniteAdeleRing R K)}
    (H : ∀ w : HeightOneSpectrum R, AdelicLevel.finComponent R K w g = AdelicLevel.finComponent R K w h) :
    g = h := by
  refine Matrix.GeneralLinearGroup.ext fun i j => congrFun (congrFun ?_ i) j
  refine matrix_eq_of_forall_mapMatrix_finAdeleEval_eq R K fun w => ?_
  rw [← coe_finComponent w g, ← coe_finComponent w h, H w]

private theorem commute_of_finComponent_eq_one (v : IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ))
    {w x : GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)} (hw : AdelicLevel.finComponent (𝓞 ℚ) ℚ v w = 1)
    (hx : ∀ w' : IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ), w' ≠ v →
      AdelicLevel.finComponent (𝓞 ℚ) ℚ w' x = 1) :
    w * x = x * w := by
  refine glEq_of_forall_finComponent_eq fun w' => ?_
  rw [map_mul, map_mul]
  rcases eq_or_ne w' v with rfl | hw'
  · rw [hw, one_mul, mul_one]
  · rw [hx w' hw', mul_one, one_mul]

section S1

private theorem mapMatrix_injective {A B : Type*} [Semiring A] [Semiring B] {f : A →+* B}
    (hf : Function.Injective f) :
    Function.Injective ((RingHom.mapMatrix f : Matrix (Fin 2) (Fin 2) A →+* _)) := fun M N h => by
  ext i j
  exact hf (by simpa [RingHom.mapMatrix_apply, Matrix.map_apply] using congrFun (congrFun h i) j)

private theorem exists_glMap_eq {R : Type*} [CommRing R] {K : Type*} [CommRing K]
    (f : R →+* K) (hf : Function.Injective f) (x : GL (Fin 2) K)
    (hx : ∀ i j, ∃ r, f r = (x : Matrix (Fin 2) (Fin 2) K) i j)
    (hx' : ∀ i j, ∃ r, f r = ((x⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) i j) :
    ∃ c : GL (Fin 2) R, Matrix.GeneralLinearGroup.map (n := Fin 2) f c = x := by
  set M : Matrix (Fin 2) (Fin 2) R := fun i j => Classical.choose (hx i j) with hM
  set M' : Matrix (Fin 2) (Fin 2) R := fun i j => Classical.choose (hx' i j)
  have hMim : f.mapMatrix M = (x : Matrix (Fin 2) (Fin 2) K) :=
    Matrix.ext fun i j => Classical.choose_spec (hx i j)
  have hM'im : f.mapMatrix M' = ((x⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) :=
    Matrix.ext fun i j => Classical.choose_spec (hx' i j)
  have hinj : Function.Injective ((RingHom.mapMatrix f : Matrix (Fin 2) (Fin 2) R →+* _)) :=
    mapMatrix_injective hf
  have hMM' : M * M' = 1 := hinj (by
    rw [map_mul, hMim, hM'im, map_one, ← Units.val_mul, mul_inv_cancel, Units.val_one])
  have hM'M : M' * M = 1 := hinj (by
    rw [map_mul, hM'im, hMim, map_one, ← Units.val_mul, inv_mul_cancel, Units.val_one])
  refine ⟨⟨M, M', hMM', hM'M⟩, Matrix.GeneralLinearGroup.ext fun i j => ?_⟩
  rw [Matrix.GeneralLinearGroup.map_apply]
  exact congrFun (congrFun hMim i) j

private theorem exists_finComponent_eq_padicGL_map (p : ℕ) [Fact p.Prime] (I : Ideal (𝓞 ℚ))
    {u : GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)} (hu : u ∈ AdelicLevel.finiteLevelOne (𝓞 ℚ) ℚ I) :
    ∃ c : GL (Fin 2) ℤ_[p],
      AdelicLevel.finComponent (𝓞 ℚ) ℚ (padicPlace p) u
        = padicGL p (Matrix.GeneralLinearGroup.map (n := Fin 2) (algebraMap ℤ_[p] ℚ_[p]) c) := by
  obtain ⟨hu₁, hu₂⟩ := AdelicLevel.mem_finiteLevelOne_iff.mp hu
  set cq : GL (Fin 2) ℚ_[p] := Matrix.GeneralLinearGroup.map (n := Fin 2)
    (padicRingEquiv p).symm.toRingHom (AdelicLevel.finComponent (𝓞 ℚ) ℚ (padicPlace p) u) with hcq

  have hcq_inv : padicGL p cq = AdelicLevel.finComponent (𝓞 ℚ) ℚ (padicPlace p) u :=
    Matrix.GeneralLinearGroup.ext fun i j => by
      rw [padicGL_apply, hcq, Matrix.GeneralLinearGroup.map_apply]
      exact RingEquiv.apply_symm_apply _ _

  have hex : ∀ (e : GL (Fin 2) ((padicPlace p).adicCompletion ℚ)),
      (∀ i j, (e : Matrix (Fin 2) (Fin 2) _) i j ∈ (padicPlace p).adicCompletionIntegers ℚ) →
      ∀ i j, ∃ r : ℤ_[p], algebraMap ℤ_[p] ℚ_[p] r
        = (Matrix.GeneralLinearGroup.map (n := Fin 2) (padicRingEquiv p).symm.toRingHom e
            : Matrix (Fin 2) (Fin 2) ℚ_[p]) i j := fun e he i j => by
    rw [Matrix.GeneralLinearGroup.map_apply]
    exact ⟨⟨_, (norm_le_one_iff_mem p _).mpr
      ((RingEquiv.apply_symm_apply (padicRingEquiv p) _).symm ▸ he i j)⟩,
      (PadicInt.algebraMap_apply _).trans rfl⟩
  have hmem : ∀ i j, (AdelicLevel.finComponent (𝓞 ℚ) ℚ (padicPlace p) u
      : Matrix (Fin 2) (Fin 2) _) i j ∈ (padicPlace p).adicCompletionIntegers ℚ := fun i j => by
    rw [AdelicLevel.finComponent_apply]; exact hu₁.integral i j (padicPlace p)
  have hmem' : ∀ i j, (AdelicLevel.finComponent (𝓞 ℚ) ℚ (padicPlace p) u⁻¹
      : Matrix (Fin 2) (Fin 2) _) i j ∈ (padicPlace p).adicCompletionIntegers ℚ := fun i j => by
    rw [AdelicLevel.finComponent_apply]; exact hu₂.integral i j (padicPlace p)
  obtain ⟨c, hc⟩ := exists_glMap_eq (algebraMap ℤ_[p] ℚ_[p])
    (IsFractionRing.injective ℤ_[p] ℚ_[p]) cq (hcq ▸ hex _ hmem)
    (by rw [hcq, ← map_inv, ← map_inv]; exact hex _ hmem')
  exact ⟨c, hcq_inv ▸ congrArg (padicGL p) hc.symm⟩

end S1

end DescentSupportA

namespace DescentEngine

open NumberField AdelicDock HeckeCosets DescentSupportA

variable (p : ℕ) [hp : Fact p.Prime]

private noncomputable abbrev ι : GL (Fin 2) ℤ_[p] →* GL (Fin 2) ℚ_[p] :=
  Matrix.GeneralLinearGroup.map (n := Fin 2) (algebraMap ℤ_[p] ℚ_[p])

private theorem ι_mem_padicK1_zero (k : GL (Fin 2) ℤ_[p]) : ι p k ∈ LocalNewvector.padicK1 p 0 :=
  ⟨k, rfl, by simp, by simp⟩

private theorem coe_ι (k : GL (Fin 2) ℤ_[p]) :
    ((ι p k : GL (Fin 2) ℚ_[p]) : Matrix (Fin 2) (Fin 2) ℚ_[p])
      = (k : Matrix (Fin 2) (Fin 2) ℤ_[p]).map (algebraMap ℤ_[p] ℚ_[p]) := by
  ext i j
  simp [Matrix.GeneralLinearGroup.map_apply]

private noncomputable def ρQ (i : Fin (p + 1)) : GL (Fin 2) ℚ_[p] :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero ((repZ p i).map (algebraMap ℤ_[p] ℚ_[p])) (by
    rw [show (repZ p i).map (algebraMap ℤ_[p] ℚ_[p]) = (algebraMap ℤ_[p] ℚ_[p]).mapMatrix (repZ p i) from rfl,
      ← RingHom.map_det, det_repZ, map_natCast]
    exact_mod_cast hp.out.ne_zero)

private theorem coe_ρQ (i : Fin (p + 1)) :
    ((ρQ p i : GL (Fin 2) ℚ_[p]) : Matrix (Fin 2) (Fin 2) ℚ_[p]) = (repZ p i).map (algebraMap ℤ_[p] ℚ_[p]) := rfl

private noncomputable def ρA (i : Fin (p + 1)) : GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ) :=
  padicToFinAdelic p (ρQ p i)

end DescentEngine

namespace DescentEngine

open NumberField AdelicDock AutomorphicForm IsDedekindDomain IsDedekindDomain.HeightOneSpectrum

variable (p : ℕ) [hp : Fact p.Prime]

private def repMat (i : Fin (p + 1)) : Matrix (Fin 2) (Fin 2) ℤ :=
  if (i : ℕ) < p then !![1, ((i : ℕ) : ℤ); 0, (p : ℤ)] else !![(p : ℤ), 0; 0, 1]

omit hp in
private theorem det_repMat (i : Fin (p + 1)) : (repMat p i).det = (p : ℤ) := by
  unfold repMat; split_ifs <;> simp [Matrix.det_fin_two_of]

omit hp in
private theorem repMat_lowerLeft (i : Fin (p + 1)) : repMat p i 1 0 = 0 := by
  unfold repMat; split_ifs <;> rfl

private theorem repZ_eq_map (i : Fin (p + 1)) :
    HeckeCosets.repZ p i = (repMat p i).map (Int.castRingHom ℤ_[p]) := by
  unfold HeckeCosets.repZ repMat
  split_ifs <;> ext a b <;> fin_cases a <;> fin_cases b <;> simp

private theorem coe_ρQ_eq_map (i : Fin (p + 1)) :
    ((ρQ p i : GL (Fin 2) ℚ_[p]) : Matrix (Fin 2) (Fin 2) ℚ_[p])
      = (repMat p i).map (Int.castRingHom ℚ_[p]) := by
  rw [coe_ρQ, repZ_eq_map, Matrix.map_map]
  congr 1

private noncomputable def repQ (i : Fin (p + 1)) : GL (Fin 2) ℚ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero ((repMat p i).map (Int.castRingHom ℚ)) (by
    rw [show (repMat p i).map (Int.castRingHom ℚ) = (Int.castRingHom ℚ).mapMatrix (repMat p i) from rfl,
      ← RingHom.map_det, det_repMat, map_natCast]
    exact_mod_cast hp.out.ne_zero)

private theorem coe_repQ (i : Fin (p + 1)) :
    ((repQ p i : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) = (repMat p i).map (Int.castRingHom ℚ) := rfl

private theorem map_repQ_eq_heckeMatrix {i : Fin (p + 1)} (hi : (i : ℕ) < p) :
    Matrix.GeneralLinearGroup.map (Rat.castHom ℝ) (repQ p i) = ModularForm.heckeMatrix p (i : ℕ) := by
  refine Units.ext ?_
  rw [ModularForm.val_heckeMatrix hp.out.ne_zero]
  ext a b
  rw [Matrix.GeneralLinearGroup.map_apply, coe_repQ, repMat, if_pos hi]
  fin_cases a <;> fin_cases b <;> simp

private theorem map_repQ_last_eq_heckeDiagMatrix :
    Matrix.GeneralLinearGroup.map (Rat.castHom ℝ) (repQ p (Fin.last p)) = ModularForm.heckeDiagMatrix p := by
  refine Units.ext ?_
  rw [ModularForm.val_heckeDiagMatrix hp.out.ne_zero]
  ext a b
  rw [Matrix.GeneralLinearGroup.map_apply, coe_repQ, repMat, if_neg (by simp)]
  fin_cases a <;> fin_cases b <;> simp

private theorem finComponent_glFin_globalPoints_repQ (i : Fin (p + 1)) :
    AdelicLevel.finComponent (𝓞 ℚ) ℚ (padicPlace p)
        (AdelicLevel.glFin (𝓞 ℚ) ℚ (globalPoints (𝓞 ℚ) ℚ (repQ p i)))
      = padicGL p (ρQ p i) := by
  refine Matrix.GeneralLinearGroup.ext fun a b => ?_
  rw [AdelicLevel.finComponent_apply, padicGL_apply, coe_ρQ_eq_map, Matrix.map_apply, eq_intCast, map_intCast]
  change (algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) ((repQ p i : Matrix (Fin 2) (Fin 2) ℚ) a b)) (padicPlace p) = _
  rw [coe_repQ, Matrix.map_apply]
  change ((algebraMap ℚ ((padicPlace p).adicCompletion ℚ)).comp (Int.castRingHom ℚ)) (repMat p i a b) = _
  rw [eq_intCast]

private theorem algebraMap_mem_adicCompletionIntegers_of_den {v : HeightOneSpectrum (𝓞 ℚ)}
    (hv : v ≠ padicPlace p) {x : ℚ} (hx : x.den = 1 ∨ x.den = p) :
    (algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) x) v ∈ v.adicCompletionIntegers ℚ := by
  have hden : (x.den : 𝓞 ℚ) ∉ v.asIdeal := by
    intro hmem
    have hgen : Rat.HeightOneSpectrum.natGenerator v ∣ x.den := by
      rw [Rat.HeightOneSpectrum.natGenerator_dvd_iff]
      simpa using Ideal.mem_map_of_mem (Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)) hmem
    rcases hx with h1 | hpd
    · rw [h1, Nat.dvd_one] at hgen
      exact (Rat.HeightOneSpectrum.prime_natGenerator v).one_lt.ne' hgen
    · rw [hpd] at hgen
      have heq : Rat.HeightOneSpectrum.natGenerator v = p :=
        (Nat.prime_dvd_prime_iff_eq (Rat.HeightOneSpectrum.prime_natGenerator v) hp.out).mp hgen
      apply hv
      unfold padicPlace
      rw [Equiv.eq_symm_apply]
      exact Subtype.ext heq
  have h := IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation' (K := ℚ) v x
  have h' : Valued.v ((algebraMap ℚ (v.adicCompletion ℚ)) x) = v.valuation ℚ x := by
    convert h using 2
    all_goals try rfl
  rw [mem_adicCompletionIntegers]
  change Valued.v ((algebraMap ℚ (v.adicCompletion ℚ)) x) ≤ 1
  rw [h']
  exact Rat.valuation_le_one_iff_den.mpr hden

end DescentEngine

namespace DescentEngine

open NumberField NumberField.AdelicLevel AdelicDock AutomorphicForm IsDedekindDomain

variable (p : ℕ) [hp : Fact p.Prime]

section GlobalPointsLemmas

private theorem isReal_rat_infinitePlace (v : InfinitePlace ℚ) : v.IsReal := IsTotallyReal.isReal v

private noncomputable def ratArchHom : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ) →* GL (Fin 2) ℝ :=
  (Matrix.GeneralLinearGroup.map
    (InfinitePlace.Completion.ringEquivRealOfIsReal (isReal_rat_infinitePlace default)).toRingHom).comp
    ((archComponent ℚ default).comp (glArch (𝓞 ℚ) ℚ))

private theorem ratArchHom_apply (g : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) :
    ratArchHom g = LanglandsTunnell.ratArchGL2 g := rfl

private theorem ratArch_mul (g g' : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) :
    LanglandsTunnell.ratArchGL2 (g * g')
      = LanglandsTunnell.ratArchGL2 g * LanglandsTunnell.ratArchGL2 g' := by
  rw [← ratArchHom_apply, ← ratArchHom_apply, ← ratArchHom_apply, map_mul]

private theorem ratArch_inv (g : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) :
    LanglandsTunnell.ratArchGL2 g⁻¹ = (LanglandsTunnell.ratArchGL2 g)⁻¹ := by
  rw [← ratArchHom_apply, ← ratArchHom_apply, map_inv]

private theorem ratArch_eq_one_of_glArch_eq_one {u : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)} (hu : glArch (𝓞 ℚ) ℚ u = 1) :
    LanglandsTunnell.ratArchGL2 u = 1 := by
  unfold LanglandsTunnell.ratArchGL2
  rw [hu, map_one, map_one]

private theorem ratArch_finEmbed (u : GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) :
    LanglandsTunnell.ratArchGL2 (finEmbed (𝓞 ℚ) ℚ u) = 1 :=
  ratArch_eq_one_of_glArch_eq_one (glArch_finEmbed (𝓞 ℚ) ℚ u)

private theorem ratArch_globalPoints (γ : GL (Fin 2) ℚ) :
    LanglandsTunnell.ratArchGL2 (globalPoints (𝓞 ℚ) ℚ γ) = Matrix.GeneralLinearGroup.map (Rat.castHom ℝ) γ := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  change ((InfinitePlace.Completion.ringEquivRealOfIsReal (isReal_rat_infinitePlace default)).toRingHom.comp
      ((archEval ℚ default).comp ((adeleArch (𝓞 ℚ) ℚ).comp (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ)))))
      ((γ : Matrix (Fin 2) (Fin 2) ℚ) i j) = (Rat.castHom ℝ) ((γ : Matrix (Fin 2) (Fin 2) ℚ) i j)
  rw [eq_ratCast, eq_ratCast]

private theorem glFin_globalPoints_apply (γ : GL (Fin 2) ℚ) (i j : Fin 2) :
    (glFin (𝓞 ℚ) ℚ (globalPoints (𝓞 ℚ) ℚ γ) : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) i j
      = algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) ((γ : Matrix (Fin 2) (Fin 2) ℚ) i j) := rfl

end GlobalPointsLemmas

private theorem gl_ext_of_arch_fin {x y : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)}
    (h₁ : glArch (𝓞 ℚ) ℚ x = glArch (𝓞 ℚ) ℚ y) (h₂ : glFin (𝓞 ℚ) ℚ x = glFin (𝓞 ℚ) ℚ y) : x = y := by
  refine Units.ext (Matrix.ext fun a b => Prod.ext ?_ ?_)
  · exact congrArg (fun g : GL (Fin 2) (InfiniteAdeleRing ℚ) => (g : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing ℚ)) a b) h₁
  · exact congrArg
      (fun g : GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ) => (g : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) a b) h₂

private theorem finEmbed_mul_comm_of_glFin_eq_one {h : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)} (hh : glFin (𝓞 ℚ) ℚ h = 1)
    (u : GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) :
    finEmbed (𝓞 ℚ) ℚ u * h = h * finEmbed (𝓞 ℚ) ℚ u := by
  refine gl_ext_of_arch_fin ?_ ?_
  · rw [map_mul, map_mul, glArch_finEmbed, one_mul, mul_one]
  · rw [map_mul, map_mul, glFin_finEmbed, hh, one_mul, mul_one]

private noncomputable def archPart (γ : GL (Fin 2) ℚ) : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ) :=
  globalPoints (𝓞 ℚ) ℚ γ * (finEmbed (𝓞 ℚ) ℚ (glFin (𝓞 ℚ) ℚ (globalPoints (𝓞 ℚ) ℚ γ)))⁻¹

private theorem glFin_archPart (γ : GL (Fin 2) ℚ) : glFin (𝓞 ℚ) ℚ (archPart γ) = 1 := by
  rw [archPart, map_mul, map_inv, glFin_finEmbed, mul_inv_cancel]

private theorem ratArch_archPart (γ : GL (Fin 2) ℚ) :
    LanglandsTunnell.ratArchGL2 (archPart γ) = Matrix.GeneralLinearGroup.map (Rat.castHom ℝ) γ := by
  rw [archPart, ratArch_mul, ratArch_inv, ratArch_finEmbed, inv_one, mul_one, ratArch_globalPoints]

private theorem globalPoints_eq_archPart_mul (γ : GL (Fin 2) ℚ) :
    globalPoints (𝓞 ℚ) ℚ γ = archPart γ * finEmbed (𝓞 ℚ) ℚ (glFin (𝓞 ℚ) ℚ (globalPoints (𝓞 ℚ) ℚ γ)) := by
  rw [archPart, inv_mul_cancel_right]

end DescentEngine

namespace DescentEngine

open NumberField NumberField.AdelicLevel AdelicDock AutomorphicForm IsDedekindDomain

variable (p : ℕ) [hp : Fact p.Prime]

private noncomputable def repInvMat (i : Fin (p + 1)) : Matrix (Fin 2) (Fin 2) ℚ :=
  if (i : ℕ) < p then !![1, ((-((i : ℕ) : ℤ) : ℤ) : ℚ) / (p : ℚ); 0, ((1 : ℤ) : ℚ) / (p : ℚ)]
  else !![((1 : ℤ) : ℚ) / (p : ℚ), 0; 0, 1]

private theorem coe_repQ_mul_repInvMat (i : Fin (p + 1)) :
    ((repQ p i : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) * repInvMat p i = 1 := by
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  rw [coe_repQ]
  unfold repMat repInvMat
  split_ifs <;> ext a b <;> fin_cases a <;> fin_cases b <;>
    (simp [Matrix.mul_apply, Fin.sum_univ_two]; (try field_simp); (try ring))

private theorem coe_repQ_inv (i : Fin (p + 1)) :
    (((repQ p i)⁻¹ : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) = repInvMat p i := by
  rw [Matrix.coe_units_inv, Matrix.inv_eq_right_inv (coe_repQ_mul_repInvMat p i)]

private def IsPShape (x : ℚ) : Prop := (∃ n : ℤ, x = n) ∨ ∃ n : ℤ, x = (n : ℚ) / (p : ℚ)

private theorem isPShape_repQ_entry (i : Fin (p + 1)) (a b : Fin 2) :
    IsPShape p (((repQ p i : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) a b) := by
  rw [coe_repQ, Matrix.map_apply, eq_intCast]
  exact Or.inl ⟨_, rfl⟩

omit hp in
private theorem isPShape_repInvMat_entry (i : Fin (p + 1)) (a b : Fin 2) : IsPShape p (repInvMat p i a b) := by
  unfold repInvMat IsPShape
  split_ifs <;> fin_cases a <;> fin_cases b <;> simp only [Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one, Fin.isValue, Fin.mk_one, Fin.zero_eta]
  · exact Or.inl ⟨1, by simp⟩
  · exact Or.inr ⟨_, rfl⟩
  · exact Or.inl ⟨0, by simp⟩
  · exact Or.inr ⟨_, rfl⟩
  · exact Or.inr ⟨_, rfl⟩
  · exact Or.inl ⟨0, by simp⟩
  · exact Or.inl ⟨0, by simp⟩
  · exact Or.inl ⟨1, by simp⟩

private theorem mem_of_isPShape {v : HeightOneSpectrum (𝓞 ℚ)} (hv : v ≠ padicPlace p) {x : ℚ} (hx : IsPShape p x) :
    (algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) x) v ∈ v.adicCompletionIntegers ℚ := by
  rcases hx with ⟨n, rfl⟩ | ⟨n, rfl⟩
  · exact algebraMap_mem_adicCompletionIntegers_of_den p hv (Or.inl (Rat.den_intCast n))
  · rw [div_eq_mul_inv, map_mul, ← finAdeleEval_apply, map_mul, finAdeleEval_apply, finAdeleEval_apply]
    refine mul_mem (algebraMap_mem_adicCompletionIntegers_of_den p hv (Or.inl (Rat.den_intCast n))) ?_
    refine algebraMap_mem_adicCompletionIntegers_of_den p hv (Or.inr ?_)
    rw [Rat.inv_natCast_den, if_neg hp.out.ne_zero]

private noncomputable def kRep (i : Fin (p + 1)) : GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ) :=
  glFin (𝓞 ℚ) ℚ (globalPoints (𝓞 ℚ) ℚ (repQ p i)) * (ρA p i)⁻¹

private theorem finComponent_kRep_self (i : Fin (p + 1)) : finComponent (𝓞 ℚ) ℚ (padicPlace p) (kRep p i) = 1 := by
  rw [kRep, map_mul, map_inv, finComponent_glFin_globalPoints_repQ, ρA, finComponent_padicToFinAdelic_self,
    mul_inv_cancel]

private theorem finComponent_kRep_of_ne {v : HeightOneSpectrum (𝓞 ℚ)} (hv : v ≠ padicPlace p) (i : Fin (p + 1)) :
    finComponent (𝓞 ℚ) ℚ v (kRep p i) = finComponent (𝓞 ℚ) ℚ v (glFin (𝓞 ℚ) ℚ (globalPoints (𝓞 ℚ) ℚ (repQ p i))) := by
  rw [kRep, map_mul, map_inv, ρA, finComponent_padicToFinAdelic_of_ne p _ hv, inv_one, mul_one]

private theorem finComponent_kRep_inv_of_ne {v : HeightOneSpectrum (𝓞 ℚ)} (hv : v ≠ padicPlace p) (i : Fin (p + 1)) :
    finComponent (𝓞 ℚ) ℚ v (kRep p i)⁻¹
      = finComponent (𝓞 ℚ) ℚ v (glFin (𝓞 ℚ) ℚ (globalPoints (𝓞 ℚ) ℚ (repQ p i)⁻¹)) := by
  rw [map_inv, finComponent_kRep_of_ne p hv, map_inv (globalPoints (𝓞 ℚ) ℚ), map_inv (glFin (𝓞 ℚ) ℚ),
    map_inv (finComponent (𝓞 ℚ) ℚ v)]

private theorem one_entry_mem (v : HeightOneSpectrum (𝓞 ℚ)) (a b : Fin 2) :
    ((1 : GL (Fin 2) (v.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) a b
      ∈ v.adicCompletionIntegers ℚ := by
  rw [Units.val_one, Matrix.one_apply]
  split_ifs
  · exact one_mem _
  · exact zero_mem _

private theorem entry_mem_integral {g : GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)} {m : Matrix (Fin 2) (Fin 2) ℚ}
    (hself : finComponent (𝓞 ℚ) ℚ (padicPlace p) g = 1)
    (hne : ∀ v : HeightOneSpectrum (𝓞 ℚ), v ≠ padicPlace p → ∀ a b : Fin 2,
      ((g : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) a b) v
        = (algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) (m a b)) v)
    (hm : ∀ a b, IsPShape p (m a b)) (a b : Fin 2) :
    (g : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) a b ∈ integralFiniteAdeles (𝓞 ℚ) ℚ := by
  intro v
  by_cases hv : v = padicPlace p
  · subst hv
    rw [← finComponent_apply, hself]
    exact one_entry_mem _ a b
  · rw [hne v hv a b]
    exact mem_of_isPShape p hv (hm a b)

private theorem lowerLeft_mem_idealBall (N : Ideal (𝓞 ℚ)) {g : GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)}
    {m : Matrix (Fin 2) (Fin 2) ℚ} (hself : finComponent (𝓞 ℚ) ℚ (padicPlace p) g = 1)
    (hne : ∀ v : HeightOneSpectrum (𝓞 ℚ), v ≠ padicPlace p → ∀ a b : Fin 2,
      ((g : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) a b) v
        = (algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) (m a b)) v)
    (hm : m 1 0 = 0) :
    (g : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) 1 0 ∈ idealBall (𝓞 ℚ) ℚ N := by
  intro v
  by_cases hv : v = padicPlace p
  · subst hv
    rw [← finComponent_apply, hself, Units.val_one, Matrix.one_apply_ne (by decide), map_zero]
    exact zero_le'
  · rw [hne v hv 1 0, hm, map_zero]
    change Valued.v ((0 : FiniteAdeleRing (𝓞 ℚ) ℚ) v) ≤ _
    rw [← finAdeleEval_apply, map_zero, map_zero]
    exact zero_le'

private theorem kRep_entry_of_ne {v : HeightOneSpectrum (𝓞 ℚ)} (hv : v ≠ padicPlace p) (i : Fin (p + 1)) (a b : Fin 2) :
    ((kRep p i : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) a b) v
      = (algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) (((repQ p i : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) a b)) v := by
  rw [← finComponent_apply, finComponent_kRep_of_ne p hv, finComponent_apply, glFin_globalPoints_apply]

private theorem kRep_inv_entry_of_ne {v : HeightOneSpectrum (𝓞 ℚ)} (hv : v ≠ padicPlace p) (i : Fin (p + 1)) (a b : Fin 2) :
    ((((kRep p i)⁻¹ : GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) a b) v
      = (algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) (repInvMat p i a b)) v := by
  rw [← finComponent_apply, finComponent_kRep_inv_of_ne p hv, finComponent_apply, glFin_globalPoints_apply,
    coe_repQ_inv]

omit hp in
private theorem repInvMat_lowerLeft (i : Fin (p + 1)) : repInvMat p i 1 0 = 0 := by
  unfold repInvMat; split_ifs <;> rfl

private theorem coe_repQ_lowerLeft (i : Fin (p + 1)) : ((repQ p i : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) 1 0 = 0 := by
  rw [coe_repQ, Matrix.map_apply, repMat_lowerLeft, map_zero]

private theorem kRep_mem_finiteLevelZero (N : Ideal (𝓞 ℚ)) (i : Fin (p + 1)) :
    kRep p i ∈ finiteLevelZero (𝓞 ℚ) ℚ N := by
  rw [mem_finiteLevelZero_iff]
  refine ⟨⟨entry_mem_integral p (finComponent_kRep_self p i) (fun v hv => kRep_entry_of_ne p hv i)
      (isPShape_repQ_entry p i), lowerLeft_mem_idealBall p N (finComponent_kRep_self p i)
      (fun v hv => kRep_entry_of_ne p hv i) (coe_repQ_lowerLeft p i)⟩, ?_⟩
  have hself : finComponent (𝓞 ℚ) ℚ (padicPlace p) (kRep p i)⁻¹ = 1 := by
    rw [map_inv, finComponent_kRep_self, inv_one]
  exact ⟨entry_mem_integral p hself (fun v hv => kRep_inv_entry_of_ne p hv i) (isPShape_repInvMat_entry p i),
    lowerLeft_mem_idealBall p N hself (fun v hv => kRep_inv_entry_of_ne p hv i) (repInvMat_lowerLeft p i)⟩

private theorem globalPoints_repQ_mul_mul_padicToAdelic_inv {h : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)}
    (hh : glFin (𝓞 ℚ) ℚ h = 1) (i : Fin (p + 1)) :
    globalPoints (𝓞 ℚ) ℚ (repQ p i) * h * padicToAdelic p (ρQ p i)⁻¹
      = (archPart (repQ p i) * h) * finEmbed (𝓞 ℚ) ℚ (kRep p i) := by
  rw [kRep]
  set G := glFin (𝓞 ℚ) ℚ (globalPoints (𝓞 ℚ) ℚ (repQ p i)) with hG
  have h1 : globalPoints (𝓞 ℚ) ℚ (repQ p i) = archPart (repQ p i) * finEmbed (𝓞 ℚ) ℚ G :=
    globalPoints_eq_archPart_mul _
  rw [map_mul, map_inv, padicToAdelic_apply, map_inv, ρA, h1, mul_assoc (archPart _),
    finEmbed_mul_comm_of_glFin_eq_one hh]
  simp only [mul_assoc]

private theorem glFin_archPart_mul {h : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)} (hh : glFin (𝓞 ℚ) ℚ h = 1) (γ : GL (Fin 2) ℚ) :
    glFin (𝓞 ℚ) ℚ (archPart γ * h) = 1 := by
  rw [map_mul, glFin_archPart, hh, one_mul]

private theorem ratArch_archPart_mul (h : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) (γ : GL (Fin 2) ℚ) :
    LanglandsTunnell.ratArchGL2 (archPart γ * h)
      = Matrix.GeneralLinearGroup.map (Rat.castHom ℝ) γ * LanglandsTunnell.ratArchGL2 h := by
  rw [ratArch_mul, ratArch_archPart]

end DescentEngine

namespace DescentEngine

open NumberField NumberField.AdelicLevel AdelicDock AutomorphicForm IsDedekindDomain LocalNewvector
open scoped ModularForm

variable (p : ℕ) [hp : Fact p.Prime]

omit hp in
private theorem σ_apply_of_det_pos {g : GL (Fin 2) ℝ} (hg : 0 < (g.det : ℝ)) (z : ℂ) :
    UpperHalfPlane.σ g z = z := by
  rw [UpperHalfPlane.σ, if_pos hg]
  rfl

omit hp in

private noncomputable def slashHom (k : ℤ) (A : GL (Fin 2) ℝ) : (UpperHalfPlane → ℂ) →+ (UpperHalfPlane → ℂ) where
  toFun f := f ∣[k] A
  map_zero' := SlashAction.zero_slash k A
  map_add' f g := SlashAction.add_slash k A f g

end DescentEngine

namespace DescentEngine

open NumberField NumberField.AdelicLevel AdelicDock AutomorphicForm IsDedekindDomain LocalNewvector
open scoped ModularForm

variable (p : ℕ) [hp : Fact p.Prime]

private theorem det_map_repQ (i : Fin (p + 1)) :
    ((Matrix.GeneralLinearGroup.map (Rat.castHom ℝ) (repQ p i)).det : ℝ) = (p : ℝ) := by
  rw [Matrix.GeneralLinearGroup.map_det, Units.coe_map, MonoidHom.coe_coe]
  change (Rat.castHom ℝ) (Matrix.det ((repMat p i).map (Int.castRingHom ℚ))) = _
  rw [show (repMat p i).map (Int.castRingHom ℚ) = (Int.castRingHom ℚ).mapMatrix (repMat p i) from rfl,
    ← RingHom.map_det, det_repMat, map_natCast, map_natCast]

private theorem map_repQ_mem_GLPos (i : Fin (p + 1)) :
    Matrix.GeneralLinearGroup.map (Rat.castHom ℝ) (repQ p i) ∈ Matrix.GLPos (Fin 2) ℝ := by
  rw [Matrix.mem_glpos, det_map_repQ]
  exact_mod_cast hp.out.pos

private theorem sum_slash_map_repQ (f : UpperHalfPlane → ℂ) :
    ∑ i : Fin (p + 1), f ∣[(2 : ℤ)] Matrix.GeneralLinearGroup.map (Rat.castHom ℝ) (repQ p i)
      = ModularForm.heckeT 2 p f := by
  rw [ModularForm.heckeT_def, Fin.sum_univ_castSucc, map_repQ_last_eq_heckeDiagMatrix, Finset.sum_range]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_repQ_eq_heckeMatrix p (by simp)]
  rfl

end DescentEngine

namespace DescentEngine

open NumberField NumberField.AdelicLevel AdelicDock AutomorphicForm IsDedekindDomain
open scoped ModularForm

variable {M : ℕ} {g : CuspForm (CongruenceSubgroup.Gamma0 M) 2}

private theorem continuous_denom (A : GL (Fin 2) ℝ) : Continuous fun τ : UpperHalfPlane => UpperHalfPlane.denom A τ := by
  unfold UpperHalfPlane.denom
  exact (continuous_const.mul UpperHalfPlane.continuous_coe).add continuous_const

private theorem continuous_slash {f : UpperHalfPlane → ℂ} (hf : Continuous f) (k : ℤ) (A : GL (Fin 2) ℝ) :
    Continuous (f ∣[k] A) := by
  have h1 : Continuous fun τ : UpperHalfPlane => UpperHalfPlane.σ A (f (A • τ)) :=
    (UpperHalfPlane.σ A).continuous.comp (hf.comp (continuous_const_smul A))
  have h2 : Continuous fun τ : UpperHalfPlane => UpperHalfPlane.denom A τ ^ (-k) :=
    (continuous_denom A).zpow₀ _ fun τ => Or.inl (UpperHalfPlane.denom_ne_zero A τ)
  have h3 : Continuous fun τ : UpperHalfPlane =>
      UpperHalfPlane.σ A (f (A • τ)) * |A.det.val| ^ (k - 1) * UpperHalfPlane.denom A τ ^ (-k) :=
    (h1.mul continuous_const).mul h2
  convert h3 using 1
  all_goals try rfl

private theorem dense_ratPoints :
    Dense (((↑) : UpperHalfPlane → ℂ) ⁻¹'
      {w : ℂ | w.re ∈ Set.range ((↑) : ℚ → ℝ) ∧ w.im ∈ Set.range ((↑) : ℚ → ℝ)}) := by
  have h1 : Dense (Set.range ((↑) : ℚ → ℝ) ×ˢ Set.range ((↑) : ℚ → ℝ)) :=
    Rat.denseRange_cast.prod Rat.denseRange_cast
  have h2 : {w : ℂ | w.re ∈ Set.range ((↑) : ℚ → ℝ) ∧ w.im ∈ Set.range ((↑) : ℚ → ℝ)} =
      Complex.equivRealProdCLM ⁻¹' (Set.range ((↑) : ℚ → ℝ) ×ˢ Set.range ((↑) : ℚ → ℝ)) := by
    ext w; simp [Set.mem_prod]
  have hS : Dense {w : ℂ | w.re ∈ Set.range ((↑) : ℚ → ℝ) ∧ w.im ∈ Set.range ((↑) : ℚ → ℝ)} := by
    rw [h2]; exact h1.preimage Complex.equivRealProdCLM.toHomeomorph.isOpenMap
  exact hS.preimage UpperHalfPlane.isOpenEmbedding_coe.isOpenMap

private theorem exists_glFin_eq_one_and_smul_I_eq (z : UpperHalfPlane) (hx : (z : ℂ).re ∈ Set.range ((↑) : ℚ → ℝ))
    (hy : (z : ℂ).im ∈ Set.range ((↑) : ℚ → ℝ)) :
    ∃ h : AdelicGL2 (𝓞 ℚ) ℚ, glFin (𝓞 ℚ) ℚ h = 1 ∧ LanglandsTunnell.ratArchGL2 h ∈ Matrix.GLPos (Fin 2) ℝ ∧
      LanglandsTunnell.ratArchGL2 h • UpperHalfPlane.I = z := by
  obtain ⟨x, hx⟩ := hx
  obtain ⟨y, hy⟩ := hy
  have hy0 : (0 : ℝ) < y := by rw [hy]; exact z.im_pos
  have hyq : (0 : ℚ) < y := by exact_mod_cast hy0
  let A : Matrix (Fin 2) (Fin 2) ℚ := !![y, x; 0, 1]
  have hdetA : A.det = y := by simp [A, Matrix.det_fin_two_of]
  let γ : GL (Fin 2) ℚ := Matrix.GeneralLinearGroup.mkOfDetNeZero A (by rw [hdetA]; exact hyq.ne')
  let h : AdelicGL2 (𝓞 ℚ) ℚ :=
    globalPoints (𝓞 ℚ) ℚ γ * finEmbed (𝓞 ℚ) ℚ (glFin (𝓞 ℚ) ℚ (globalPoints (𝓞 ℚ) ℚ γ))⁻¹
  have hfin : glFin (𝓞 ℚ) ℚ h = 1 := by
    simp only [h, map_mul, glFin_finEmbed, mul_inv_cancel]
  have hP : LanglandsTunnell.ratArchGL2 h = Matrix.GeneralLinearGroup.map (Rat.castHom ℝ) γ := by
    simp only [h, ratArch_mul, ratArch_finEmbed, mul_one, ratArch_globalPoints]
  have hPmat : ((LanglandsTunnell.ratArchGL2 h : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
      !![(y : ℝ), (x : ℝ); 0, 1] := by
    rw [hP]
    ext i j
    change (Rat.castHom ℝ) (A i j) = _
    fin_cases i <;> fin_cases j <;> simp [A]
  have hdetP : ((LanglandsTunnell.ratArchGL2 h).det.val : ℝ) = y := by
    rw [Matrix.GeneralLinearGroup.val_det_apply, hPmat, Matrix.det_fin_two_of]; ring
  have hdetpos : (0 : ℝ) < (LanglandsTunnell.ratArchGL2 h).det.val := by rw [hdetP]; exact hy0
  refine ⟨h, hfin, (Matrix.mem_glpos _).mpr hdetpos, ?_⟩
  rw [UpperHalfPlane.coe_re] at hx
  rw [UpperHalfPlane.coe_im] at hy
  apply UpperHalfPlane.ext
  rw [UpperHalfPlane.coe_smul_of_det_pos hdetpos]
  simp only [UpperHalfPlane.num, UpperHalfPlane.denom, hPmat, Matrix.of_apply, Matrix.cons_val',
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one, UpperHalfPlane.coe_I,
    Complex.ofReal_zero, zero_mul, zero_add, Complex.ofReal_one, div_one]
  apply Complex.ext <;> simp [← hx, ← hy]

private theorem eq_of_forall_slash_apply_I {F G : UpperHalfPlane → ℂ} (hF : Continuous F) (hG : Continuous G)
    (hFG : ∀ h : AdelicGL2 (𝓞 ℚ) ℚ, glFin (𝓞 ℚ) ℚ h = 1 → LanglandsTunnell.ratArchGL2 h ∈ Matrix.GLPos (Fin 2) ℝ →
      (F ∣[(1 : ℤ)] LanglandsTunnell.ratArchGL2 h) UpperHalfPlane.I
        = (G ∣[(1 : ℤ)] LanglandsTunnell.ratArchGL2 h) UpperHalfPlane.I) :
    F = G := by
  refine Continuous.ext_on dense_ratPoints hF hG ?_
  rintro z ⟨hx, hy⟩
  obtain ⟨h, hfin, hpos, hz⟩ := exists_glFin_eq_one_and_smul_I_eq z hx hy
  have hdet : (0 : ℝ) < (LanglandsTunnell.ratArchGL2 h).det.val := (Matrix.mem_glpos _).mp hpos
  have key := hFG h hfin hpos
  rw [ModularForm.slash_apply, ModularForm.slash_apply, σ_apply_of_det_pos hdet, σ_apply_of_det_pos hdet, hz]
    at key
  have hne : |(LanglandsTunnell.ratArchGL2 h).det.val| ^ ((1 : ℤ) - 1)
      * UpperHalfPlane.denom (LanglandsTunnell.ratArchGL2 h) UpperHalfPlane.I ^ (-(1 : ℤ)) ≠ 0 :=
    mul_ne_zero (by exact_mod_cast zpow_ne_zero _ (abs_ne_zero.mpr hdet.ne'))
      (zpow_ne_zero _ (UpperHalfPlane.denom_ne_zero _ _))
  rw [mul_assoc, mul_assoc] at key
  exact mul_right_cancel₀ hne key

end DescentEngine

namespace DescentSupportB

open NumberField NumberField.AdelicLevel AdelicDock IsDedekindDomain

section S4c

private theorem natGenerator_padicPlace (p : ℕ) [Fact p.Prime] :
    Rat.HeightOneSpectrum.natGenerator (R := 𝓞 ℚ) (padicPlace p) = p :=
  congrArg Subtype.val
    ((Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).apply_symm_apply ⟨p, Fact.out⟩)

private theorem eq_padicPlace_natGenerator (v : HeightOneSpectrum (𝓞 ℚ)) :
    haveI : Fact (Rat.HeightOneSpectrum.natGenerator v).Prime :=
      ⟨Rat.HeightOneSpectrum.prime_natGenerator v⟩
    v = padicPlace (Rat.HeightOneSpectrum.natGenerator v) := by
  haveI : Fact (Rat.HeightOneSpectrum.natGenerator v).Prime :=
    ⟨Rat.HeightOneSpectrum.prime_natGenerator v⟩
  refine ((Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).symm_apply_apply v).symm.trans ?_
  exact congrArg _ (Subtype.ext rfl)

private theorem padicPlace_injective {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    (h : padicPlace p = padicPlace q) : p = q :=
  congrArg Subtype.val
    ((Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).symm.injective h)

private theorem valued_natCast_eq_of_factorization_eq (ℓ : ℕ) [Fact ℓ.Prime]
    {N M : ℕ} (hN : N ≠ 0) (hM : M ≠ 0) (hfac : N.factorization ℓ = M.factorization ℓ) :
    Valued.v (padicRingEquiv ℓ (N : ℚ_[ℓ])) = Valued.v (padicRingEquiv ℓ (M : ℚ_[ℓ])) := by
  have hN' : (N : ℚ_[ℓ]) ≠ 0 := by exact_mod_cast hN
  have hM' : (M : ℚ_[ℓ]) ≠ 0 := by exact_mod_cast hM
  refine le_antisymm ?_ ?_
  · rw [valued_le_valued_iff ℓ _ _ hM', norm_natCast_eq_zpow_neg_factorization ℓ hN,
      norm_natCast_eq_zpow_neg_factorization ℓ hM, hfac]
  · rw [valued_le_valued_iff ℓ _ _ hN', norm_natCast_eq_zpow_neg_factorization ℓ hN,
      norm_natCast_eq_zpow_neg_factorization ℓ hM, hfac]

private theorem idealBound_ratLevel_eq_of_factorization_eq {q : ℕ} [Fact q.Prime] {N M : ℕ}
    (hN : N ≠ 0) (hM : M ≠ 0)
    (hfac : ∀ ℓ : ℕ, ℓ.Prime → ℓ ≠ q → N.factorization ℓ = M.factorization ℓ)
    (v : HeightOneSpectrum (𝓞 ℚ)) (hv : v ≠ padicPlace q) :
    idealBound (𝓞 ℚ) (ratLevel N) v = idealBound (𝓞 ℚ) (ratLevel M) v := by
  haveI hℓp : Fact (Rat.HeightOneSpectrum.natGenerator v).Prime :=
    ⟨Rat.HeightOneSpectrum.prime_natGenerator v⟩
  have hvℓ : v = padicPlace (Rat.HeightOneSpectrum.natGenerator v) :=
    eq_padicPlace_natGenerator v
  have hne : Rat.HeightOneSpectrum.natGenerator v ≠ q := fun heq =>
    hv <| (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).injective <|
      Subtype.ext <| heq.trans (natGenerator_padicPlace q).symm
  rw [hvℓ, idealBound_ratLevel _ hN, idealBound_ratLevel _ hM,
    valued_natCast_eq_of_factorization_eq _ hN hM (hfac _ hℓp.out hne)]

end S4c

end DescentSupportB

namespace DescentSupportB

open NumberField NumberField.AdelicLevel AdelicDock IsDedekindDomain

section S4d

private theorem algebraMap_intCast_apply_padicPlace_eq (p : ℕ) [Fact p.Prime] (n : ℤ) :
    (algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) (n : ℚ)) (padicPlace p)
      = padicRingEquiv p ((n : ℤ_[p]) : ℚ_[p]) := by
  have hL : (algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) (n : ℚ)) (padicPlace p) =
      (n : (padicPlace p).adicCompletion ℚ) := by
    change ((algebraMap ℚ ((padicPlace p).adicCompletion ℚ)).comp (Int.castRingHom ℚ)) n = _
    exact eq_intCast _ n
  have hR : padicRingEquiv p ((n : ℤ_[p]) : ℚ_[p]) = (n : (padicPlace p).adicCompletion ℚ) := by
    rw [PadicInt.coe_intCast, map_intCast]
  exact hL.trans hR.symm

private theorem isLevelZeroMatrix_mapMatrix_of_int_entries {N : ℕ} (hN : N ≠ 0)
    (δ : Matrix (Fin 2) (Fin 2) ℚ) (hδ : ∀ a b, ∃ n : ℤ, δ a b = n)
    (hlow : ∃ m : ℤ, δ 1 0 = (N : ℚ) * m) :
    IsLevelZeroMatrix (𝓞 ℚ) ℚ (ratLevel N)
      ((algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ)).mapMatrix δ) := by
  refine ⟨fun i j v => ?_, fun v => ?_⟩
  all_goals
    haveI : Fact (Rat.HeightOneSpectrum.natGenerator v).Prime :=
      ⟨Rat.HeightOneSpectrum.prime_natGenerator v⟩
    rw [eq_padicPlace_natGenerator v]
    set ℓ := Rat.HeightOneSpectrum.natGenerator v
  · rw [RingHom.mapMatrix_apply, Matrix.map_apply]
    obtain ⟨n, hn⟩ := hδ i j
    rw [hn, algebraMap_intCast_apply_padicPlace_eq ℓ n]
    exact padicRingEquiv_coe_mem ℓ _
  · rw [RingHom.mapMatrix_apply, Matrix.map_apply]
    obtain ⟨m, hm⟩ := hlow
    have hNm : δ 1 0 = ((N * m : ℤ) : ℚ) := by push_cast; linarith [hm]
    rw [hNm, algebraMap_intCast_apply_padicPlace_eq ℓ (N * m)]
    rw [(valued_coe_le_idealBound_iff ℓ hN _)]
    have hdvd : (ℓ : ℤ_[ℓ]) ^ N.factorization ℓ ∣ (↑(N * m) : ℤ_[ℓ]) := by
      have hdvdZ : (ℓ : ℤ) ^ N.factorization ℓ ∣ (N * m : ℤ) := by
        refine Dvd.dvd.mul_right ?_ m
        exact_mod_cast Nat.ordProj_dvd N ℓ
      obtain ⟨k, hk⟩ := hdvdZ
      exact ⟨(k : ℤ_[ℓ]), by push_cast [hk]; ring⟩
    exact Ideal.mem_span_singleton.mpr hdvd

private theorem map_algebraMap_mem_finiteLevelZero {N : ℕ} (hN : N ≠ 0) (δ : GL (Fin 2) ℚ)
    (hδ : ∀ a b : Fin 2, ∃ n : ℤ, (δ : Matrix (Fin 2) (Fin 2) ℚ) a b = n)
    (hδ' : ∀ a b : Fin 2, ∃ n : ℤ, ((δ⁻¹ : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) a b = n)
    (hlow : ∃ m : ℤ, (δ : Matrix (Fin 2) (Fin 2) ℚ) 1 0 = (N : ℚ) * m)
    (hlow' : ∃ m : ℤ, ((δ⁻¹ : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) 1 0 = (N : ℚ) * m) :
    Matrix.GeneralLinearGroup.map (algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ)) δ
      ∈ finiteLevelZero (𝓞 ℚ) ℚ (ratLevel N) := by
  rw [mem_finiteLevelZero_iff]
  have hcoe : ∀ (γ : GL (Fin 2) ℚ),
      (Matrix.GeneralLinearGroup.map (algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ)) γ
        : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ))
      = (algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ)).mapMatrix (γ : Matrix (Fin 2) (Fin 2) ℚ) :=
    fun γ => Matrix.ext fun i j => Matrix.GeneralLinearGroup.map_apply _ i j γ
  rw [hcoe δ, ← Matrix.GeneralLinearGroup.map_inv, hcoe δ⁻¹]
  exact ⟨isLevelZeroMatrix_mapMatrix_of_int_entries hN _ hδ hlow,
    isLevelZeroMatrix_mapMatrix_of_int_entries hN _ hδ' hlow'⟩

end S4d

end DescentSupportB

namespace DescentEngine

open NumberField NumberField.AdelicLevel AdelicDock AutomorphicForm IsDedekindDomain LocalNewvector
open scoped ModularForm

variable {M : ℕ} {g : CuspForm (CongruenceSubgroup.Gamma0 M) 2} {φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ}

private theorem glFin_globalPoints_eq_map (δ : GL (Fin 2) ℚ) :
    glFin (𝓞 ℚ) ℚ (globalPoints (𝓞 ℚ) ℚ δ)
      = Matrix.GeneralLinearGroup.map (algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ)) δ := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  rw [glFin_globalPoints_apply]
  rfl

private theorem mapGL_entry_int (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) (a b : Fin 2) :
    ∃ n : ℤ, ((Matrix.SpecialLinearGroup.mapGL ℚ γ : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) a b = n :=
  ⟨γ a b, by simp [Matrix.SpecialLinearGroup.mapGL]⟩

private theorem mapGL_lowerLeft_of_mem_Gamma0 {N : ℕ} {γ : Matrix.SpecialLinearGroup (Fin 2) ℤ}
    (hγ : γ ∈ CongruenceSubgroup.Gamma0 N) :
    ∃ m : ℤ, ((Matrix.SpecialLinearGroup.mapGL ℚ γ : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) 1 0 = (N : ℚ) * m := by
  obtain ⟨m, hm⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd (γ 1 0) N).mp (CongruenceSubgroup.Gamma0_mem.mp hγ)
  refine ⟨m, ?_⟩
  simp [Matrix.SpecialLinearGroup.mapGL, hm]

private theorem glFin_globalPoints_mapGL_mem_finiteLevelZero {N : ℕ} (hN : N ≠ 0) {γ : Matrix.SpecialLinearGroup (Fin 2) ℤ}
    (hγ : γ ∈ CongruenceSubgroup.Gamma0 N) :
    glFin (𝓞 ℚ) ℚ (globalPoints (𝓞 ℚ) ℚ (Matrix.SpecialLinearGroup.mapGL ℚ γ)) ∈ finiteLevelZero (𝓞 ℚ) ℚ (ratLevel N) := by
  rw [glFin_globalPoints_eq_map]
  refine DescentSupportB.map_algebraMap_mem_finiteLevelZero hN _ (mapGL_entry_int γ) ?_
    (mapGL_lowerLeft_of_mem_Gamma0 hγ) ?_
  · rw [← map_inv]
    exact mapGL_entry_int γ⁻¹
  · rw [← map_inv]
    exact mapGL_lowerLeft_of_mem_Gamma0 (Subgroup.inv_mem _ hγ)

private theorem map_castHom_mapGL (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) :
    Matrix.GeneralLinearGroup.map (Rat.castHom ℝ) (Matrix.SpecialLinearGroup.mapGL ℚ γ)
      = Matrix.SpecialLinearGroup.mapGL ℝ γ := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  simp [Matrix.SpecialLinearGroup.mapGL]

private theorem mapGL_mem_GLPos (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) :
    (Matrix.SpecialLinearGroup.mapGL ℝ γ : GL (Fin 2) ℝ) ∈ Matrix.GLPos (Fin 2) ℝ := by
  rw [Matrix.mem_glpos]
  simp [Matrix.SpecialLinearGroup.mapGL]

end DescentEngine

namespace DescentEngine

open NumberField NumberField.AdelicLevel AdelicDock AutomorphicForm IsDedekindDomain
open scoped ModularForm

section LevelOneUpgrade

private theorem valued_det_finComponent_eq_one_of_mem_finiteLevelZero
    {N : Ideal (𝓞 ℚ)} {u : GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)}
    (hu : u ∈ finiteLevelZero (𝓞 ℚ) ℚ N) (w : HeightOneSpectrum (𝓞 ℚ)) :
    Valued.v ((finComponent (𝓞 ℚ) ℚ w u).det : w.adicCompletion ℚ) = 1 := by
  have hle : ∀ g : GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ),
      IsLevelZeroMatrix (𝓞 ℚ) ℚ N (g : Matrix _ _ _) →
      Valued.v ((finComponent (𝓞 ℚ) ℚ w g).det : w.adicCompletion ℚ) ≤ 1 := by
    intro g hg
    rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two]
    refine (Valuation.map_sub _ _ _).trans (max_le ?_ ?_)
    all_goals
      rw [Valuation.map_mul]
      refine mul_le_one' ?_ ?_
      all_goals
        rw [finComponent_apply]
        exact valued_apply_le_one (hg.integral _ _) w
  have h1 : Valued.v ((finComponent (𝓞 ℚ) ℚ w u).det : w.adicCompletion ℚ) ≤ 1 := hle u hu.1
  have h2 : Valued.v ((finComponent (𝓞 ℚ) ℚ w u⁻¹).det : w.adicCompletion ℚ) ≤ 1 := hle u⁻¹ hu.2
  refine le_antisymm h1 ?_
  have hprod : Valued.v ((finComponent (𝓞 ℚ) ℚ w u).det : w.adicCompletion ℚ)
      * Valued.v ((finComponent (𝓞 ℚ) ℚ w u⁻¹).det : w.adicCompletion ℚ) = 1 := by
    rw [← Valuation.map_mul, ← Units.val_mul, ← map_mul, ← map_mul, mul_inv_cancel,
      map_one, map_one, Units.val_one, map_one]
  calc (1 : _) = _ := hprod.symm
    _ ≤ Valued.v ((finComponent (𝓞 ℚ) ℚ w u).det : w.adicCompletion ℚ) * 1 := by gcongr
    _ = _ := mul_one _

private theorem mem_finiteLevelOne_of_lowerRight {N : Ideal (𝓞 ℚ)} {g : GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)}
    (hg : g ∈ finiteLevelZero (𝓞 ℚ) ℚ N)
    (h11 : (g : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) 1 1 - 1 ∈ idealBall (𝓞 ℚ) ℚ N) :
    g ∈ finiteLevelOne (𝓞 ℚ) ℚ N := by
  obtain ⟨hg₁, hg₂⟩ := mem_finiteLevelZero_iff.mp hg
  refine mem_finiteLevelOne_iff.mpr ⟨⟨hg₁, h11⟩, ⟨hg₂, fun v => ?_⟩⟩
  set G : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ) :=
    (finComponent (𝓞 ℚ) ℚ v g : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) with hG
  have hdet1 : Valued.v G.det = 1 := valued_det_finComponent_eq_one_of_mem_finiteLevelZero hg v
  have hdet0 : G.det ≠ 0 := fun h => by rw [h, Valuation.map_zero] at hdet1; exact zero_ne_one hdet1
  have hGinv : ((finComponent (𝓞 ℚ) ℚ v g⁻¹ : GL (Fin 2) (v.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) _)
      = G⁻¹ := by
    rw [map_inv, Matrix.coe_units_inv]
  have hinv11 : G⁻¹ 1 1 = G.det⁻¹ * G 0 0 := by
    rw [Matrix.inv_def, Ring.inverse_eq_inv', Matrix.smul_apply, smul_eq_mul, Matrix.adjugate_fin_two]
    simp

  have hx : (((g⁻¹ : GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) 1 1
        - 1) v = G.det⁻¹ * (G 0 0 - G.det) := by
    rw [coe_sub_apply, coe_one_apply, ← finComponent_apply, hGinv, hinv11, mul_sub, inv_mul_cancel₀ hdet0]
  rw [hx, Valuation.map_mul, map_inv₀, hdet1, inv_one, one_mul]
  have hexp : G 0 0 - G.det = G 0 0 * (1 - G 1 1) + G 0 1 * G 1 0 := by
    rw [Matrix.det_fin_two]; ring
  rw [hexp]
  have hint : ∀ i j, Valued.v (G i j) ≤ 1 := fun i j => by
    rw [hG, finComponent_apply]; exact valued_apply_le_one (hg₁.integral i j) v
  refine (Valuation.map_add _ _ _).trans (max_le ?_ ?_)
  · rw [Valuation.map_mul]
    have h11' : Valued.v (1 - G 1 1) ≤ idealBound (𝓞 ℚ) N v := by
      rw [Valuation.map_sub_swap, hG, finComponent_apply]
      exact h11 v
    calc Valued.v (G 0 0) * Valued.v (1 - G 1 1) ≤ 1 * idealBound (𝓞 ℚ) N v :=
          mul_le_mul' (hint 0 0) h11'
      _ = _ := one_mul _
  · rw [Valuation.map_mul]
    have h10 : Valued.v (G 1 0) ≤ idealBound (𝓞 ℚ) N v := by
      rw [hG, finComponent_apply]; exact hg₁.lowerLeft v
    calc Valued.v (G 0 1) * Valued.v (G 1 0) ≤ 1 * idealBound (𝓞 ℚ) N v := mul_le_mul' (hint 0 1) h10
      _ = _ := one_mul _

end LevelOneUpgrade

section GammaOneReps

variable (p : ℕ) [hp : Fact p.Prime]

private theorem padicPlace_ne_of_ne' {ℓ q : ℕ} [Fact ℓ.Prime] [Fact q.Prime] (h : ℓ ≠ q) :
    padicPlace ℓ ≠ padicPlace q := by
  intro heq
  have h' := congrArg (fun v : HeightOneSpectrum (𝓞 ℚ) => (Rat.HeightOneSpectrum.primesEquiv v : ℕ)) heq
  simp only [padicPlace, Equiv.apply_symm_apply] at h'
  exact h h'

private theorem glFin_globalPoints_mul_kRep_mem_finiteLevelOne {N : ℕ} (hN : N ≠ 0) (hpN : ¬ p ∣ N)
    {σ : Matrix.SpecialLinearGroup (Fin 2) ℤ} (hσ : σ ∈ CongruenceSubgroup.Gamma0 N) (i : Fin (p + 1))
    (hcong : (N : ℤ) ∣ σ 1 1 * repMat p i 1 1 - 1) :
    glFin (𝓞 ℚ) ℚ (globalPoints (𝓞 ℚ) ℚ (Matrix.SpecialLinearGroup.mapGL ℚ σ)) * kRep p i
      ∈ finiteLevelOne (𝓞 ℚ) ℚ (ratLevel N) := by
  have hK₀ : glFin (𝓞 ℚ) ℚ (globalPoints (𝓞 ℚ) ℚ (Matrix.SpecialLinearGroup.mapGL ℚ σ)) * kRep p i
      ∈ finiteLevelZero (𝓞 ℚ) ℚ (ratLevel N) :=
    mul_mem (glFin_globalPoints_mapGL_mem_finiteLevelZero hN hσ) (kRep_mem_finiteLevelZero p _ i)
  refine mem_finiteLevelOne_of_lowerRight hK₀ fun v => ?_
  rw [coe_sub_apply, coe_one_apply, ← finComponent_apply, map_mul]
  by_cases hv : v = padicPlace p
  ·
    subst hv
    rw [finComponent_kRep_self, mul_one, finComponent_apply, glFin_globalPoints_apply]
    obtain ⟨n, hn⟩ := mapGL_entry_int σ 1 1
    rw [hn, DescentSupportB.algebraMap_intCast_apply_padicPlace_eq p n, ← map_one (padicRingEquiv p), ← map_sub,
      ← PadicInt.coe_one, ← PadicInt.coe_sub, valued_coe_le_idealBound_iff p hN,
      Nat.factorization_eq_zero_of_not_dvd hpN, pow_zero, Ideal.span_singleton_one]
    exact Submodule.mem_top
  ·
    rw [finComponent_kRep_of_ne p hv, ← map_mul, ← map_mul, ← map_mul, finComponent_apply, glFin_globalPoints_apply,
      Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two, coe_repQ]
    haveI : Fact (Rat.HeightOneSpectrum.natGenerator v).Prime := ⟨Rat.HeightOneSpectrum.prime_natGenerator v⟩
    rw [DescentSupportB.eq_padicPlace_natGenerator v]
    set ℓ := Rat.HeightOneSpectrum.natGenerator v
    have hentry : (((Matrix.SpecialLinearGroup.mapGL ℚ σ : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) 1 0
          * ((repMat p i).map (Int.castRingHom ℚ)) 0 1 +
        ((Matrix.SpecialLinearGroup.mapGL ℚ σ : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) 1 1
          * ((repMat p i).map (Int.castRingHom ℚ)) 1 1) - 1
        = (((σ 1 0 * repMat p i 0 1 + (σ 1 1 * repMat p i 1 1 - 1) : ℤ)) : ℚ) := by
      simp [Matrix.SpecialLinearGroup.mapGL]
      ring
    rw [show (1 : (padicPlace ℓ).adicCompletion ℚ) = (algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) 1) (padicPlace ℓ) from
        by rw [map_one]; rfl, ← coe_sub_apply, ← map_sub, hentry,
      DescentSupportB.algebraMap_intCast_apply_padicPlace_eq ℓ, valued_coe_le_idealBound_iff ℓ hN]
    have hdvd : (N : ℤ) ∣ σ 1 0 * repMat p i 0 1 + (σ 1 1 * repMat p i 1 1 - 1) := by
      refine dvd_add (Dvd.dvd.mul_right ?_ _) hcong
      exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (CongruenceSubgroup.Gamma0_mem.mp hσ)
    have hdvd' : ((ℓ : ℤ) ^ N.factorization ℓ) ∣ σ 1 0 * repMat p i 0 1 + (σ 1 1 * repMat p i 1 1 - 1) :=
      (Int.natCast_dvd_natCast.mpr (Nat.ordProj_dvd N ℓ) |>.trans (by exact_mod_cast hdvd))
    obtain ⟨k, hk⟩ := hdvd'
    refine Ideal.mem_span_singleton.mpr ⟨(k : ℤ_[ℓ]), ?_⟩
    have := congrArg (fun z : ℤ => (z : ℤ_[ℓ])) hk
    push_cast at this ⊢
    exact this

private theorem exists_gamma0_lowerRight_mul_eq_one {N : ℕ} [NeZero N] {ℓ : ℕ} (hℓ : ℓ.Coprime N) :
    ∃ σ : Matrix.SpecialLinearGroup (Fin 2) ℤ, σ ∈ CongruenceSubgroup.Gamma0 N ∧
      ((σ 1 1 : ℤ) : ZMod N) * ℓ = 1 := by
  set u : (ZMod N)ˣ := (ZMod.unitOfCoprime ℓ hℓ)⁻¹ with hu
  set d : ℕ := (u : ZMod N).val with hd
  have hdcop : d.Coprime N := ZMod.val_coe_unit_coprime u
  obtain ⟨x, y, hxy⟩ : IsCoprime (d : ℤ) (N : ℤ) := Int.isCoprime_iff_gcd_eq_one.mpr (by simpa using hdcop)
  refine ⟨⟨!![x, -y; (N : ℤ), (d : ℤ)], by rw [Matrix.det_fin_two_of]; linarith⟩, ?_, ?_⟩
  · rw [CongruenceSubgroup.Gamma0_mem]
    show (((N : ℤ) : ℤ) : ZMod N) = 0
    simp
  · show (((d : ℤ) : ℤ) : ZMod N) * ℓ = 1
    rw [Int.cast_natCast, hd, ZMod.natCast_zmod_val, ← ZMod.coe_unitOfCoprime ℓ hℓ, ← Units.val_mul, hu,
      inv_mul_cancel, Units.val_one]

end GammaOneReps

section HeckeReading

variable (p : ℕ) [hp : Fact p.Prime]

private theorem glFin_conj_eq_one' (δ : GL (Fin 2) ℚ) {h : AdelicGL2 (𝓞 ℚ) ℚ} (hh : glFin (𝓞 ℚ) ℚ h = 1) :
    glFin (𝓞 ℚ) ℚ ((globalPoints (𝓞 ℚ) ℚ δ)⁻¹ * h * globalPoints (𝓞 ℚ) ℚ δ) = 1 := by
  rw [map_mul, map_mul, hh, mul_one, map_inv, inv_mul_cancel]

omit hp in

private theorem weightOneArchLift_eq (f : UpperHalfPlane → ℂ) (h : GL (Fin 2) ℝ) :
    weightOneArchLift f h = (f ∣[(1 : ℤ)] h) UpperHalfPlane.I * ((h.det.val : ℝ) : ℂ) := by
  rw [weightOneArchLift, zpow_one]

omit hp in

private theorem det_mapGL_mul (σ : Matrix.SpecialLinearGroup (Fin 2) ℤ) (h : GL (Fin 2) ℝ) :
    (((Matrix.SpecialLinearGroup.mapGL ℝ σ : GL (Fin 2) ℝ) * h).det.val : ℝ) = h.det.val := by
  rw [map_mul, Units.val_mul, Matrix.SpecialLinearGroup.det_mapGL, Units.val_one, one_mul]

variable {N : ℕ} {ε : DirichletCharacter ℂ N} {F : CuspForm (CongruenceSubgroup.Gamma1 N) 1}

omit hp in

private theorem lift_dictionary [NeZero N] :
    (∀ (γ : GL (Fin 2) ℚ) (x : AdelicGL2 (𝓞 ℚ) ℚ), weightOneLift (Ideal.span {(N : 𝓞 ℚ)}) (⇑F) (globalPoints (𝓞 ℚ) ℚ γ * x) = weightOneLift (Ideal.span {(N : 𝓞 ℚ)}) (⇑F) x) ∧
    (∀ u ∈ finiteLevelOne (𝓞 ℚ) ℚ (AdelicDock.ratLevel N), ∀ x : AdelicGL2 (𝓞 ℚ) ℚ,
        weightOneLift (Ideal.span {(N : 𝓞 ℚ)}) (⇑F) (x * AdelicDock.finEmbed (𝓞 ℚ) ℚ u) = weightOneLift (Ideal.span {(N : 𝓞 ℚ)}) (⇑F) x) ∧
    ∀ h : AdelicGL2 (𝓞 ℚ) ℚ, glFin (𝓞 ℚ) ℚ h = 1 →
      LanglandsTunnell.ratArchGL2 h ∈ Matrix.GLPos (Fin 2) ℝ →
        weightOneLift (Ideal.span {(N : 𝓞 ℚ)}) (⇑F) h = weightOneArchLift (⇑F) (LanglandsTunnell.ratArchGL2 h) :=
  DihedralWeightOne.weightOneLift_globalPoints_mul_and_mul_finEmbed_and_eq_weightOneArchLift (NeZero.ne N) (⇑F)
    (fun γ hγ => SlashInvariantForm.slash_action_eqn F _ (Subgroup.mem_map.mpr ⟨γ, hγ, rfl⟩))

private theorem slash_eq_smul_of_hasNebentypus (hε : CuspForm.HasNebentypus ε F)
    {γ : Matrix.SpecialLinearGroup (Fin 2) ℤ} (hγ : γ ∈ CongruenceSubgroup.Gamma0 N) :
    (⇑F) ∣[(1 : ℤ)] (Matrix.SpecialLinearGroup.mapGL ℝ γ : GL (Fin 2) ℝ) = ε ((γ 1 1 : ℤ) : ZMod N) • (⇑F) := by
  funext τ
  have hSL : ((⇑F) ∣[(1 : ℤ)] (Matrix.SpecialLinearGroup.mapGL ℝ γ : GL (Fin 2) ℝ)) τ
      = F (γ • τ) * UpperHalfPlane.denom γ τ ^ (-(1 : ℤ)) := ModularForm.SL_slash_apply (k := 1) (⇑F) γ τ
  have hden : UpperHalfPlane.denom γ τ ≠ 0 := UpperHalfPlane.denom_ne_zero γ τ
  rw [ModularGroup.denom_apply] at hden
  rw [hSL, hε γ hγ τ, ModularGroup.denom_apply, Pi.smul_apply, smul_eq_mul]
  have h2 : (((γ 1 0 : ℤ) : ℂ) * (τ : ℂ) + ((γ 1 1 : ℤ) : ℂ)) ^ (1 : ℤ) ≠ 0 := zpow_ne_zero _ hden
  field_simp

private theorem apply_mul_finEmbed_eq_of_mem_finiteLevelOne [NeZero N] (hε : CuspForm.HasNebentypus ε F)
    {σ : Matrix.SpecialLinearGroup (Fin 2) ℤ} (hσ : σ ∈ CongruenceSubgroup.Gamma0 N)
    {k : GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)}
    (hk : glFin (𝓞 ℚ) ℚ (globalPoints (𝓞 ℚ) ℚ (Matrix.SpecialLinearGroup.mapGL ℚ σ)) * k
      ∈ finiteLevelOne (𝓞 ℚ) ℚ (ratLevel N))
    {X : AdelicGL2 (𝓞 ℚ) ℚ} (hX : glFin (𝓞 ℚ) ℚ X = 1) (hXpos : LanglandsTunnell.ratArchGL2 X ∈ Matrix.GLPos (Fin 2) ℝ) :
    weightOneLift (Ideal.span {(N : 𝓞 ℚ)}) (⇑F) (X * finEmbed (𝓞 ℚ) ℚ k) = ε ((σ 1 1 : ℤ) : ZMod N) * weightOneLift (Ideal.span {(N : 𝓞 ℚ)}) (⇑F) X := by
  obtain ⟨hleft, hlevel, happly⟩ := lift_dictionary (F := F)
  set sQ : GL (Fin 2) ℚ := Matrix.SpecialLinearGroup.mapGL ℚ σ with hsQ
  set E : GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ) := glFin (𝓞 ℚ) ℚ (globalPoints (𝓞 ℚ) ℚ sQ) with hE
  have hk_eq : finEmbed (𝓞 ℚ) ℚ k = (globalPoints (𝓞 ℚ) ℚ sQ)⁻¹ * archPart sQ * finEmbed (𝓞 ℚ) ℚ (E * k) := by
    rw [map_mul, hE, ← mul_assoc]
    conv_rhs => rw [mul_assoc ((globalPoints (𝓞 ℚ) ℚ sQ)⁻¹), ← globalPoints_eq_archPart_mul, inv_mul_cancel,
      one_mul]
  set δ : GL (Fin 2) ℚ := sQ⁻¹ with hδ
  set Y : AdelicGL2 (𝓞 ℚ) ℚ := (globalPoints (𝓞 ℚ) ℚ δ)⁻¹ * X * globalPoints (𝓞 ℚ) ℚ δ * archPart sQ with hY
  have hXk : X * finEmbed (𝓞 ℚ) ℚ k = globalPoints (𝓞 ℚ) ℚ δ * (Y * finEmbed (𝓞 ℚ) ℚ (E * k)) := by
    rw [hk_eq, hY, hδ, map_inv]
    group
  have hYfin : glFin (𝓞 ℚ) ℚ Y = 1 := by
    rw [hY, map_mul, glFin_conj_eq_one' δ hX, one_mul, glFin_archPart]
  have hYarch : LanglandsTunnell.ratArchGL2 Y
      = Matrix.SpecialLinearGroup.mapGL ℝ σ * LanglandsTunnell.ratArchGL2 X := by
    rw [hY, ratArch_mul, ratArch_mul, ratArch_mul, ratArch_inv, ratArch_globalPoints, ratArch_archPart, hδ,
      map_inv, inv_inv, hsQ, map_castHom_mapGL]
    group
  have hYpos : LanglandsTunnell.ratArchGL2 Y ∈ Matrix.GLPos (Fin 2) ℝ := by
    rw [hYarch]; exact Subgroup.mul_mem _ (mapGL_mem_GLPos σ) hXpos
  rw [hXk, hleft, hlevel _ hk, happly Y hYfin hYpos, hYarch, weightOneArchLift_eq,
    det_mapGL_mul, SlashAction.slash_mul, slash_eq_smul_of_hasNebentypus hε hσ, ModularForm.smul_slash,
    Pi.smul_apply, smul_eq_mul, σ_apply_of_det_pos ((Matrix.mem_glpos _).mp hXpos), happly X hX hXpos,
    weightOneArchLift_eq, mul_assoc]

private theorem apply_mul_finEmbed_kRep [NeZero N] (hε : CuspForm.HasNebentypus ε F)
    (hpN : ¬ p ∣ N) (i : Fin (p + 1))
    {X : AdelicGL2 (𝓞 ℚ) ℚ} (hX : glFin (𝓞 ℚ) ℚ X = 1) (hXpos : LanglandsTunnell.ratArchGL2 X ∈ Matrix.GLPos (Fin 2) ℝ) :
    weightOneLift (Ideal.span {(N : 𝓞 ℚ)}) (⇑F) (X * finEmbed (𝓞 ℚ) ℚ (kRep p i))
      = (if (i : ℕ) < p then (ε ((p : ℕ) : ZMod N))⁻¹ else 1) * weightOneLift (Ideal.span {(N : 𝓞 ℚ)}) (⇑F) X := by
  have hN : N ≠ 0 := NeZero.ne N
  have hcop : p.Coprime N := (Nat.Prime.coprime_iff_not_dvd hp.out).mpr hpN
  split_ifs with hi
  · obtain ⟨σ, hσ, hσℓ⟩ := exists_gamma0_lowerRight_mul_eq_one (N := N) hcop
    have hcong : (N : ℤ) ∣ σ 1 1 * repMat p i 1 1 - 1 := by
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
      unfold repMat
      rw [if_pos hi]
      push_cast
      simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_one, Matrix.cons_val_fin_one,
        Matrix.cons_val_zero, Int.cast_natCast]
      rw [hσℓ, sub_self]
    rw [apply_mul_finEmbed_eq_of_mem_finiteLevelOne hε hσ
      (glFin_globalPoints_mul_kRep_mem_finiteLevelOne p hN hpN hσ i hcong) hX hXpos]
    congr 1
    have hu : ε ((p : ℕ) : ZMod N) * ε ((σ 1 1 : ℤ) : ZMod N) = 1 := by
      rw [← map_mul, mul_comm, hσℓ, map_one]
    exact (eq_inv_of_mul_eq_one_right hu)
  · have hcong : (N : ℤ) ∣ (1 : Matrix.SpecialLinearGroup (Fin 2) ℤ) 1 1 * repMat p i 1 1 - 1 := by
      unfold repMat
      rw [if_neg hi]
      simp
    have h1 := apply_mul_finEmbed_eq_of_mem_finiteLevelOne hε (Subgroup.one_mem _)
      (glFin_globalPoints_mul_kRep_mem_finiteLevelOne p hN hpN (Subgroup.one_mem _) i hcong) hX hXpos
    rw [h1]
    simp

private theorem sum_apply_eq_slash [NeZero N] (hε : CuspForm.HasNebentypus ε F)
    (hpN : ¬ p ∣ N)
    {h : AdelicGL2 (𝓞 ℚ) ℚ} (hh : glFin (𝓞 ℚ) ℚ h = 1)
    (hpos : LanglandsTunnell.ratArchGL2 h ∈ Matrix.GLPos (Fin 2) ℝ) :
    ∑ i : Fin (p + 1), weightOneLift (Ideal.span {(N : 𝓞 ℚ)}) (⇑F) (h * padicToAdelic p (ρQ p i)⁻¹)
      = (((ε ((p : ℕ) : ZMod N))⁻¹ • ModularForm.heckeU 1 p ⇑F + (⇑F) ∣[(1 : ℤ)] ModularForm.heckeDiagMatrix p)
          ∣[(1 : ℤ)] LanglandsTunnell.ratArchGL2 h) UpperHalfPlane.I *
        ((p : ℂ) * (((LanglandsTunnell.ratArchGL2 h).det.val : ℝ) : ℂ)) := by
  obtain ⟨hleft, hlevel, happly⟩ := lift_dictionary (F := F)
  have hterm : ∀ i : Fin (p + 1), weightOneLift (Ideal.span {(N : 𝓞 ℚ)}) (⇑F) (h * padicToAdelic p (ρQ p i)⁻¹)
      = ((if (i : ℕ) < p then (ε ((p : ℕ) : ZMod N))⁻¹ else 1) *
        ((⇑F ∣[(1 : ℤ)] Matrix.GeneralLinearGroup.map (Rat.castHom ℝ) (repQ p i))
          ∣[(1 : ℤ)] LanglandsTunnell.ratArchGL2 h) UpperHalfPlane.I) *
        ((p : ℂ) * (((LanglandsTunnell.ratArchGL2 h).det.val : ℝ) : ℂ)) := by
    intro i
    have h1 : h * padicToAdelic p (ρQ p i)⁻¹
        = globalPoints (𝓞 ℚ) ℚ (repQ p i)⁻¹ * ((archPart (repQ p i) * h) * finEmbed (𝓞 ℚ) ℚ (kRep p i)) := by
      rw [← globalPoints_repQ_mul_mul_padicToAdelic_inv p hh i, map_inv (globalPoints (𝓞 ℚ) ℚ),
        mul_assoc (globalPoints (𝓞 ℚ) ℚ (repQ p i)) h, inv_mul_cancel_left]
    have hpos' : LanglandsTunnell.ratArchGL2 (archPart (repQ p i) * h) ∈ Matrix.GLPos (Fin 2) ℝ := by
      rw [ratArch_archPart_mul]
      exact Subgroup.mul_mem _ (map_repQ_mem_GLPos p i) hpos
    have hdet : ((LanglandsTunnell.ratArchGL2 (archPart (repQ p i) * h)).det.val : ℝ)
        = (p : ℝ) * (LanglandsTunnell.ratArchGL2 h).det.val := by
      rw [ratArch_archPart_mul, map_mul, Units.val_mul, det_map_repQ]
    rw [h1, hleft, apply_mul_finEmbed_kRep p hε hpN i (glFin_archPart_mul hh _) hpos',
      happly _ (glFin_archPart_mul hh _) hpos', weightOneArchLift_eq, hdet, ratArch_archPart_mul,
      SlashAction.slash_mul]
    push_cast
    ring
  rw [Finset.sum_congr rfl fun i _ => hterm i, ← Finset.sum_mul]
  congr 1
  rw [Fin.sum_univ_castSucc]
  have hlast : (if ((Fin.last p : Fin (p + 1)) : ℕ) < p then (ε ((p : ℕ) : ZMod N))⁻¹ else (1 : ℂ)) = 1 :=
    if_neg (by simp)
  have hcast : ∀ i : Fin p,
      (if ((Fin.castSucc i : Fin (p + 1)) : ℕ) < p then (ε ((p : ℕ) : ZMod N))⁻¹ else (1 : ℂ))
        = (ε ((p : ℕ) : ZMod N))⁻¹ := fun i => if_pos (by simp [Fin.is_lt])
  rw [hlast, one_mul, map_repQ_last_eq_heckeDiagMatrix]
  rw [Finset.sum_congr rfl fun (i : Fin p) _ => by rw [hcast i], ← Finset.mul_sum]

  have hdist : (∑ i : Fin p, (⇑F) ∣[(1 : ℤ)] ModularForm.heckeMatrix p (i : ℕ)) ∣[(1 : ℤ)] LanglandsTunnell.ratArchGL2 h
      = ∑ i : Fin p, ((⇑F) ∣[(1 : ℤ)] ModularForm.heckeMatrix p (i : ℕ)) ∣[(1 : ℤ)] LanglandsTunnell.ratArchGL2 h :=
    map_sum (slashHom 1 (LanglandsTunnell.ratArchGL2 h)) _ _
  rw [SlashAction.add_slash, Pi.add_apply, ModularForm.smul_slash, Pi.smul_apply, smul_eq_mul,
    σ_apply_of_det_pos ((Matrix.mem_glpos _).mp hpos), ModularForm.heckeU_def, Finset.sum_range, hdist,
    Finset.sum_apply]
  congr 2
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_repQ_eq_heckeMatrix p (by simp)]
  rfl

private theorem continuous_heckeSide (c : ℂ) :
    Continuous (c • ModularForm.heckeU 1 p ⇑F + (⇑F) ∣[(1 : ℤ)] ModularForm.heckeDiagMatrix p) := by
  have hF : Continuous (⇑F : UpperHalfPlane → ℂ) := (CuspFormClass.holo F).continuous
  refine Continuous.add ?_ (continuous_slash hF 1 _)
  refine Continuous.const_smul ?_ c
  rw [ModularForm.heckeU_def]
  have h : (∑ j ∈ Finset.range p, (⇑F) ∣[(1 : ℤ)] ModularForm.heckeMatrix p j)
      = fun τ => ∑ j ∈ Finset.range p, ((⇑F) ∣[(1 : ℤ)] ModularForm.heckeMatrix p j) τ := by
    funext τ; exact Finset.sum_apply τ _ _
  rw [h]
  exact continuous_finsetSum _ fun j _ => continuous_slash hF 1 _

end HeckeReading

section MainT

private theorem eq_ρQ_of_coe_eq (ℓ : ℕ) [hℓ : Fact ℓ.Prime] (ρ : Fin (ℓ + 1) → GL (Fin 2) ℚ_[ℓ])
    (hρ : ∀ i : Fin (ℓ + 1), ((ρ i : GL (Fin 2) ℚ_[ℓ]) : Matrix (Fin 2) (Fin 2) ℚ_[ℓ]) =
      if (i : ℕ) < ℓ then !![(1 : ℚ_[ℓ]), ((i : ℕ) : ℚ_[ℓ]); 0, (ℓ : ℚ_[ℓ])]
      else !![(ℓ : ℚ_[ℓ]), 0; 0, 1]) (i : Fin (ℓ + 1)) :
    ρ i = ρQ ℓ i := by
  refine Units.ext ?_
  rw [hρ i, coe_ρQ]
  unfold HeckeCosets.repZ
  split_ifs
  · ext a b; fin_cases a <;> fin_cases b <;> simp
  · ext a b; fin_cases a <;> fin_cases b <;> simp

private theorem one_mem_strictPeriods_gamma1 (L : ℕ) :
    (1 : ℝ) ∈ ((CongruenceSubgroup.Gamma1 L : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ)) :
      Subgroup (GL (Fin 2) ℝ)).strictPeriods := by
  rw [CongruenceSubgroup.strictPeriods_Gamma1]
  exact AddSubgroup.mem_zmultiples 1

end MainT

end DescentEngine

open DescentEngine NumberField NumberField.AdelicLevel AdelicDock AutomorphicForm in
open scoped ModularForm in
theorem solution
    {N : ℕ} [NeZero N] {ε : DirichletCharacter ℂ N} {F : CuspForm (CongruenceSubgroup.Gamma1 N) 1}
    (hε : CuspForm.HasNebentypus ε F)
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓN : ¬ ℓ ∣ N)
    (ρ : Fin (ℓ + 1) → GL (Fin 2) ℚ_[ℓ])
    (hρ : ∀ i : Fin (ℓ + 1), ((ρ i : GL (Fin 2) ℚ_[ℓ]) : Matrix (Fin 2) (Fin 2) ℚ_[ℓ]) =
      if (i : ℕ) < ℓ then !![(1 : ℚ_[ℓ]), ((i : ℕ) : ℚ_[ℓ]); 0, (ℓ : ℚ_[ℓ])]
      else !![(ℓ : ℚ_[ℓ]), 0; 0, 1])
    (lam : ℂ)
    (heig : ∀ x : AdelicGL2 (𝓞 ℚ) ℚ, glFin (𝓞 ℚ) ℚ x = 1 →
      LanglandsTunnell.ratArchGL2 x ∈ Matrix.GLPos (Fin 2) ℝ →
        ∑ i : Fin (ℓ + 1), weightOneLift (Ideal.span {(N : 𝓞 ℚ)}) (⇑F) (x * AdelicDock.padicToAdelic ℓ (ρ i)⁻¹) =
          lam * weightOneLift (Ideal.span {(N : 𝓞 ℚ)}) (⇑F) x)
    (n : ℕ) :
    ModularFormClass.qCoeff F (ℓ * n) +
        ε (ℓ : ZMod N) * (ℓ : ℂ) ^ ((1 : ℤ) - 1) *
          (if ℓ ∣ n then ModularFormClass.qCoeff F (n / ℓ) else 0) =
      ε (ℓ : ZMod N) * (ℓ : ℂ)⁻¹ * lam * ModularFormClass.qCoeff F n := by
  have hℓ : ℓ.Prime := Fact.out
  have hℓ0 : ℓ ≠ 0 := hℓ.ne_zero
  have hℓC : (ℓ : ℂ) ≠ 0 := by exact_mod_cast hℓ0
  have hcop : ℓ.Coprime N := (Nat.Prime.coprime_iff_not_dvd hℓ).mpr hℓN
  set eℓ : ℂ := ε (ℓ : ZMod N) with heℓ
  have heℓ0 : eℓ ≠ 0 := by
    rw [heℓ, ← ZMod.coe_unitOfCoprime ℓ hcop, ← MulChar.coe_toUnitHom]
    exact Units.ne_zero _
  obtain ⟨-, -, happly⟩ := lift_dictionary (F := F)

  have hF : Continuous (⇑F : UpperHalfPlane → ℂ) := (CuspFormClass.holo F).continuous
  have hfun : eℓ⁻¹ • ModularForm.heckeU 1 ℓ ⇑F + (⇑F) ∣[(1 : ℤ)] ModularForm.heckeDiagMatrix ℓ
      = (lam * (ℓ : ℂ)⁻¹) • ⇑F := by
    refine eq_of_forall_slash_apply_I (continuous_heckeSide ℓ _) (hF.const_smul (lam * (ℓ : ℂ)⁻¹)) fun h hh hpos => ?_
    have hdet : (0 : ℝ) < (LanglandsTunnell.ratArchGL2 h).det.val := (Matrix.mem_glpos _).mp hpos
    have hD : ((ℓ : ℂ) * (((LanglandsTunnell.ratArchGL2 h).det.val : ℝ) : ℂ)) ≠ 0 :=
      mul_ne_zero hℓC (Complex.ofReal_ne_zero.mpr hdet.ne')
    have key := heig h hh hpos
    rw [Finset.sum_congr rfl (fun i _ => by rw [eq_ρQ_of_coe_eq ℓ ρ hρ i]), sum_apply_eq_slash ℓ hε hℓN hh hpos,
      happly h hh hpos, weightOneArchLift_eq] at key
    rw [ModularForm.smul_slash, Pi.smul_apply, smul_eq_mul, σ_apply_of_det_pos hdet]
    apply mul_right_cancel₀ hD
    rw [key]
    field_simp

  haveI : NeZero (N * ℓ) := ⟨mul_ne_zero (NeZero.ne N) hℓ0⟩
  obtain ⟨G₁, hG₁, hG₁q, -⟩ := CuspForm.exists_degeneracy_gamma1_hasNebentypus (M := N) (N := N * ℓ) (d := 1)
    (by rw [mul_one]; exact Dvd.intro _ rfl) F
  obtain ⟨Gℓ, hGℓ, hGℓq, -⟩ := CuspForm.exists_degeneracy_gamma1_hasNebentypus (M := N) (N := N * ℓ) (d := ℓ)
    dvd_rfl F
  have hFG₁ : (⇑F : UpperHalfPlane → ℂ) = ⇑G₁ := by
    funext τ
    rw [hG₁ τ]
    congr 1
    apply UpperHalfPlane.ext
    rw [ModularForm.coe_heckeDiagMatrix_smul one_ne_zero]
    simp
  have hFGℓ : (⇑F) ∣[(1 : ℤ)] ModularForm.heckeDiagMatrix ℓ = ⇑Gℓ := by
    funext τ
    rw [ModularForm.slash_heckeDiagMatrix_apply 1 hℓ0, hGℓ τ]
    norm_num

  have hU : ModularForm.heckeU 1 ℓ ⇑F = ⇑(eℓ • ((lam * (ℓ : ℂ)⁻¹) • G₁ - Gℓ)) := by
    have h1 : ModularForm.heckeU 1 ℓ ⇑F
        = eℓ • ((lam * (ℓ : ℂ)⁻¹) • ⇑F - (⇑F) ∣[(1 : ℤ)] ModularForm.heckeDiagMatrix ℓ) := by
      rw [smul_sub, ← hfun, smul_add, ← mul_smul, mul_inv_cancel₀ heℓ0, one_smul, add_sub_cancel_right]
    rw [h1, hFGℓ, CuspForm.IsGLPos.coe_smul, CuspForm.coe_sub, CuspForm.IsGLPos.coe_smul, ← hFG₁]

  have hΓ := one_mem_strictPeriods_gamma1 N
  have hΓ' := one_mem_strictPeriods_gamma1 (N * ℓ)
  have hcoefU : ModularFormClass.qCoeff (ModularForm.heckeU 1 ℓ ⇑F) n = ModularFormClass.qCoeff F (n * ℓ) := by
    rw [ModularFormClass.qCoeff_heckeU F hΓ hℓ0 n, ModularForm.coeffHeckeU_apply]
  have hcoefH : ModularFormClass.qCoeff (⇑(eℓ • ((lam * (ℓ : ℂ)⁻¹) • G₁ - Gℓ))) n
      = eℓ * ((lam * (ℓ : ℂ)⁻¹) * ModularFormClass.qCoeff G₁ n - ModularFormClass.qCoeff Gℓ n) := by
    simp only [ModularFormClass.qCoeff]
    rw [CuspForm.IsGLPos.coe_smul, ModularForm.qExpansion_smul one_pos hΓ' eℓ ((lam * (ℓ : ℂ)⁻¹) • G₁ - Gℓ),
      map_smul, smul_eq_mul, CuspForm.coe_sub, ModularForm.qExpansion_sub one_pos hΓ' ((lam * (ℓ : ℂ)⁻¹) • G₁) Gℓ,
      map_sub, CuspForm.IsGLPos.coe_smul, ModularForm.qExpansion_smul one_pos hΓ' (lam * (ℓ : ℂ)⁻¹) G₁, map_smul,
      smul_eq_mul]
  have hG₁n : ModularFormClass.qCoeff G₁ n = ModularFormClass.qCoeff F n := by
    rw [hG₁q n, if_pos (one_dvd n), Nat.div_one]
  have hmain : ModularFormClass.qCoeff F (n * ℓ)
      = eℓ * ((lam * (ℓ : ℂ)⁻¹) * ModularFormClass.qCoeff F n
          - (if ℓ ∣ n then ModularFormClass.qCoeff F (n / ℓ) else 0)) := by
    rw [← hcoefU, hU, hcoefH, hG₁n, hGℓq n]
  rw [mul_comm ℓ n, hmain, show ((1 : ℤ) - 1) = 0 by norm_num, zpow_zero]
  ring

end S_DihedralWeightOne_qCoeff_hecke_eq_of_hasNebentypus_of_sum_weightOneLift_mul_padicToAdelic_inv_eq
end P2MW
export P2MW.S_DihedralWeightOne_qCoeff_hecke_eq_of_hasNebentypus_of_sum_weightOneLift_mul_padicToAdelic_inv_eq (solution)
