-- Prove2me | solution 1 for FiniteFields.zetaFunction_integral_presentation
-- status  : ACCEPTED   (prove)
-- author  : @Idealson
-- created : 2026-10-20T07:32:41.598743+00:00
-- url     : https://prove2.me/submissions/a7fd9f69-a904-4690-bc01-111c60c2409b

import Mathlib
import Definitions.Def_FiniteFields_Dwork_Devissage
import Definitions.Def_WeilConjectures_projectiveSpace
import Definitions.Def_WeilConjectures_zetaFunction
import Theorems.Thm_FiniteFields_dwork_rationality_explicit
section
noncomputable section
open AlgebraicGeometry CategoryTheory
namespace WeilConjectures.Bridge
variable (p : ℕ) [Fact p.Prime] {k : Type} [Field k] [Finite k] [CharP k p]
  {X : Scheme} (f : X ⟶ Spec (.of k))
theorem pointCount_of_neZero (m : ℕ) [NeZero m] :
    pointCount p f m = pointsOver f (FiniteField.Extension k p m) := by
  rw [pointCount, dif_neg (NeZero.ne m)]
theorem pointCount_succ (n : ℕ) :
    pointCount p f (n + 1) = pointsOver f (FiniteField.Extension k p (n + 1)) :=
  pointCount_of_neZero p f (n + 1)
theorem zetaFunction_eq : zetaFunction p f = zetaOfCounts (pointCount p f) := rfl
end WeilConjectures.Bridge
end
end
section
noncomputable section
open PowerSeries
namespace WeilConjectures.Bridge
def countingSeries (N : ℕ → ℕ) : ℚ⟦X⟧ :=
  PowerSeries.mk fun m ↦ (N (m + 1) : ℚ)
@[simp]
theorem coeff_countingSeries (N : ℕ → ℕ) (m : ℕ) :
    coeff m (countingSeries N) = (N (m + 1) : ℚ) := by
  simp [countingSeries]
def IsZetaSeries (N : ℕ → ℕ) (Z : ℚ⟦X⟧) : Prop :=
  constantCoeff Z = 1 ∧ d⁄dX ℚ Z = countingSeries N * Z
theorem IsZetaSeries.unique {N : ℕ → ℕ} {Z W : ℚ⟦X⟧}
    (hZ : IsZetaSeries N Z) (hW : IsZetaSeries N W) : Z = W :=
  PowerSeries.eq_of_derivative_eq_mul
    (by rw [hZ.2, mul_comm]) (by rw [hW.2, mul_comm]) (hZ.1.trans hW.1.symm)
def zetaLog (N : ℕ → ℕ) : ℚ⟦X⟧ :=
  PowerSeries.mk fun m ↦ if m = 0 then (0 : ℚ) else (N m : ℚ) / (m : ℚ)
theorem zetaOfCounts_eq (N : ℕ → ℕ) :
    zetaOfCounts N = (PowerSeries.exp ℚ).subst (zetaLog N) := rfl
@[simp]
theorem constantCoeff_zetaLog (N : ℕ → ℕ) : constantCoeff (zetaLog N) = 0 := by
  rw [← coeff_zero_eq_constantCoeff_apply, zetaLog, coeff_mk]
  simp
theorem hasSubst_zetaLog (N : ℕ → ℕ) : HasSubst (zetaLog N) :=
  HasSubst.of_constantCoeff_zero' (constantCoeff_zetaLog N)
theorem derivative_zetaLog (N : ℕ → ℕ) : d⁄dX ℚ (zetaLog N) = countingSeries N := by
  ext m
  rw [coeff_derivative, zetaLog, coeff_mk, coeff_countingSeries]
  have hne : (m : ℚ) + 1 ≠ 0 := by positivity
  simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, if_false]
  push_cast
  field_simp
theorem constantCoeff_zetaOfCounts (N : ℕ → ℕ) : constantCoeff (zetaOfCounts N) = 1 := by
  rw [zetaOfCounts_eq, ← coeff_zero_eq_constantCoeff_apply,
    coeff_subst' (hasSubst_zetaLog N), finsum_eq_single _ 0]
  · simp
  · intro e he
    simp [he, constantCoeff_zetaLog]
theorem derivative_zetaOfCounts (N : ℕ → ℕ) :
    d⁄dX ℚ (zetaOfCounts N) = countingSeries N * zetaOfCounts N := by
  rw [zetaOfCounts_eq, derivative_subst (hasSubst_zetaLog N), derivative_exp,
    derivative_zetaLog, mul_comm]
theorem zetaOfCounts_isZetaSeries (N : ℕ → ℕ) : IsZetaSeries N (zetaOfCounts N) :=
  ⟨constantCoeff_zetaOfCounts N, derivative_zetaOfCounts N⟩
theorem zetaOfCounts_congr {N N' : ℕ → ℕ} (h : ∀ m, 1 ≤ m → N m = N' m) :
    zetaOfCounts N = zetaOfCounts N' := by
  have hc : countingSeries N = countingSeries N' := by
    ext m
    simp [h (m + 1) (Nat.succ_pos m)]
  refine (zetaOfCounts_isZetaSeries N).unique ⟨constantCoeff_zetaOfCounts N', ?_⟩
  rw [hc]
  exact derivative_zetaOfCounts N'
end WeilConjectures.Bridge
end
end
section
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicGeometry CategoryTheory
namespace WeilConjectures.Bridge
attribute [local instance] MvPolynomial.gradedAlgebra
section Proper
variable {k : Type} [Field k]
theorem surjective_algebraMap_grade_zero (N : ℕ) :
    Function.Surjective (algebraMap k (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) k 0)) := by
  intro x
  have hx : (x : MvPolynomial (Fin (N + 1)) k) ∈ (1 : Submodule k _) := by
    rw [← MvPolynomial.homogeneousSubmodule_zero]
    exact x.2
  obtain ⟨y, hy⟩ := Submodule.mem_one.mp hx
  exact ⟨y, Subtype.ext hy⟩
theorem isProper_of_isProjectiveOver {X : Scheme} (f : X ⟶ Spec (.of k))
    (h : IsProjectiveOver k f) : IsProper f := by
  obtain ⟨N, i, hi, rfl⟩ := h
  have : IsFinite (Spec.map (CommRingCat.ofHom
      (algebraMap k (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) k 0)))) := by
    rw [IsFinite.SpecMap_iff]
    exact RingHom.Finite.of_surjective _ (surjective_algebraMap_grade_zero N)
  have : Algebra.FiniteType (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) k 0)
      (MvPolynomial (Fin (N + 1)) k) :=
    haveI : IsScalarTower k (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) k 0)
        (MvPolynomial (Fin (N + 1)) k) :=
      IsScalarTower.of_algebraMap_eq (R := k)
        (S := MvPolynomial.homogeneousSubmodule (Fin (N + 1)) k 0)
        (A := MvPolynomial (Fin (N + 1)) k) fun _ ↦ rfl
    Algebra.FiniteType.of_restrictScalars_finiteType k _ _
  unfold projectiveSpace.toSpec
  infer_instance
end Proper
end WeilConjectures.Bridge
end
section
open AlgebraicGeometry CategoryTheory
namespace WeilConjectures.Bridge
variable {k : Type} [Field k] {X : Scheme} (f : X ⟶ Spec (.of k))
theorem finiteType_and_isSeparated_of_isProjectiveOver (h : IsProjectiveOver k f) :
    FiniteFields.Schemes.FiniteType f ∧ IsSeparated f := by
  have := isProper_of_isProjectiveOver f h
  exact ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩
def rationalPointEquiv (K : Type) [Field K] [Algebra k K] :
    FiniteFields.RationalPoint k X f K ≃
      {x : Spec (.of K) ⟶ X // x ≫ f = Spec.map (CommRingCat.ofHom (algebraMap k K))} where
  toFun x := ⟨x.hom, x.over_base⟩
  invFun x := ⟨x.1, x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
variable (p : ℕ) [Fact p.Prime] [Finite k] [CharP k p]
theorem pointCount_succ_eq (n : ℕ)
    [Finite (FiniteFields.ExtensionPoint (k := k) (p := p) X f n)] :
    pointCount p f (n + 1) = FiniteFields.pointCount k p X f n := by
  rw [pointCount_succ, pointsOver, FiniteFields.pointCount]
  exact (Nat.card_congr (rationalPointEquiv f _)).symm
theorem pointCount_succ_eq_of_finiteType (hf : FiniteFields.Schemes.FiniteType f) (n : ℕ) :
    pointCount p f (n + 1) = FiniteFields.pointCount_of_finiteType k p X f hf n := by
  let := hf.1
  let := hf.2
  exact pointCount_succ_eq f p n
theorem zetaLog_eq_dwork (N : ℕ → ℕ) :
    zetaLog N = FiniteFields.Dwork.zetaLog (fun n ↦ N (n + 1)) := by
  ext m
  rw [zetaLog, FiniteFields.Dwork.zetaLog, PowerSeries.coeff_mk, PowerSeries.coeff_mk]
  rcases m with _ | m
  · simp
  · simp
theorem zetaOfCounts_eq_zetaSeriesOf (N : ℕ → ℕ) :
    zetaOfCounts N = FiniteFields.Dwork.zetaSeriesOf (fun n ↦ N (n + 1)) := by
  rw [zetaOfCounts_eq, zetaLog_eq_dwork]
  rfl
theorem zetaFunction_eq_zetaSeriesOf (hf : FiniteFields.Schemes.FiniteType f) :
    zetaFunction p f = FiniteFields.Dwork.zetaSeriesOf
      (fun n ↦ FiniteFields.pointCount_of_finiteType k p X f hf n) := by
  rw [zetaFunction_eq, zetaOfCounts_eq_zetaSeriesOf]
  congr 1
  funext n
  exact pointCount_succ_eq_of_finiteType f p hf n
end WeilConjectures.Bridge
end
section
noncomputable section
namespace FiniteFields.Dwork
open CategoryTheory AlgebraicGeometry PowerSeries
variable (k : Type) [Field k] [Finite k]
variable (p : ℕ) [Fact p.Prime] [CharP k p]
variable {d : ℕ}
variable (f : MvPolynomial (Fin d) k)
theorem coeff_geomFactor (R : Type*) [CommRing R] (e j : ℕ) :
    PowerSeries.coeff j (geomFactor R e) = if e ∣ j then 1 else 0 :=
  PowerSeries.coeff_mk _ _
theorem map_geomFactor (e : ℕ) :
    PowerSeries.map (Int.castRingHom ℚ) (geomFactor ℤ e) = geomFactor ℚ e := by
  ext j
  rw [PowerSeries.coeff_map, coeff_geomFactor, coeff_geomFactor]
  split <;> simp
omit [Finite k] [Fact p.Prime] [CharP k p] in
theorem one_sub_mul_geomFactor (e : ℕ) (he : 0 < e) :
    (1 - PowerSeries.X ^ e) * geomFactor ℚ e = 1 := by
  ext m
  rw [sub_mul, one_mul, map_sub, coeff_geomFactor, PowerSeries.coeff_X_pow_mul']
  by_cases hm : e ≤ m
  · rw [if_pos hm, coeff_geomFactor]
    have hiff : e ∣ m ↔ e ∣ m - e := by
      constructor
      · intro hd; exact Nat.dvd_sub hd dvd_rfl
      · intro hd
        have := Nat.dvd_add hd (dvd_refl e)
        rwa [Nat.sub_add_cancel hm] at this
    by_cases hd : e ∣ m
    · rw [if_pos hd, if_pos (hiff.mp hd), sub_self]
      rw [PowerSeries.coeff_one, if_neg (by omega)]
    · rw [if_neg hd, if_neg (fun hc => hd (hiff.mpr hc)), sub_zero]
      rw [PowerSeries.coeff_one, if_neg (by omega)]
  · rw [if_neg hm, sub_zero, PowerSeries.coeff_one]
    by_cases hm0 : m = 0
    · subst hm0
      rw [if_pos (dvd_zero e), if_pos rfl]
    · rw [if_neg hm0, if_neg (fun hc => hm (Nat.le_of_dvd (Nat.pos_of_ne_zero hm0) hc))]
omit [Finite k] [Fact p.Prime] [CharP k p] in
theorem derivative_geomFactor (e : ℕ) (he : 0 < e) :
    PowerSeries.derivative ℚ (geomFactor ℚ e)
      = (e : ℚ⟦X⟧) * PowerSeries.X ^ (e - 1) * (geomFactor ℚ e * geomFactor ℚ e) := by
  have hinv : (1 - PowerSeries.X ^ e) * geomFactor ℚ e = 1 := one_sub_mul_geomFactor e he
  have hdX : PowerSeries.derivative ℚ ((1 : ℚ⟦X⟧) - PowerSeries.X ^ e)
      = -((e : ℚ⟦X⟧) * PowerSeries.X ^ (e - 1)) := by
    rw [map_sub, Derivation.map_one_eq_zero, PowerSeries.derivative_pow,
      PowerSeries.derivative_X, mul_one, zero_sub]
  have hd := congrArg (PowerSeries.derivative ℚ) hinv
  rw [Derivation.leibniz, Derivation.map_one_eq_zero, hdX] at hd
  simp only [smul_eq_mul] at hd
  have hkey : (1 - PowerSeries.X ^ e) * PowerSeries.derivative ℚ (geomFactor ℚ e)
      = (e : ℚ⟦X⟧) * PowerSeries.X ^ (e - 1) * geomFactor ℚ e := by
    linear_combination hd
  calc PowerSeries.derivative ℚ (geomFactor ℚ e)
      = ((1 - PowerSeries.X ^ e) * geomFactor ℚ e)
          * PowerSeries.derivative ℚ (geomFactor ℚ e) := by rw [hinv, one_mul]
    _ = ((1 - PowerSeries.X ^ e) * PowerSeries.derivative ℚ (geomFactor ℚ e))
          * geomFactor ℚ e := by ring
    _ = (e : ℚ⟦X⟧) * PowerSeries.X ^ (e - 1) * (geomFactor ℚ e * geomFactor ℚ e) := by
        rw [hkey]; ring
end FiniteFields.Dwork
end
end
section
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicGeometry CategoryTheory
namespace WeilConjectures.Bridge
variable {k : Type} [Field k] {X : Scheme.{0}} (f : X ⟶ Spec (.of k))
noncomputable def residueStructure (x : X) : CommRingCat.of k ⟶ X.residueField x :=
  (Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop ≫ X.presheaf.germ ⊤ x trivial ≫ X.residue x
noncomputable abbrev residueAlgebra (x : X) : Algebra k (X.residueField x) :=
  (residueStructure f x).hom.toAlgebra
@[reassoc]
theorem fromSpecResidueField_appTop (x : X) :
    (X.fromSpecResidueField x).appTop ≫ (Scheme.ΓSpecIso (X.residueField x)).hom =
      X.presheaf.germ ⊤ x trivial ≫ X.residue x := by
  simp only [Scheme.fromSpecResidueField, Scheme.Hom.comp_appTop, Category.assoc,
    Scheme.ΓSpecIso_naturality, Scheme.fromSpecStalk_appTop]
  congr 1
  rw [← Category.assoc, ← Category.assoc]
  convert Category.id_comp (X.residue x) using 2
  rw [Category.assoc]
  convert (Scheme.ΓSpecIso (X.presheaf.stalk x)).inv_hom_id using 2
  convert Category.id_comp _
  convert (Spec (X.presheaf.stalk x)).presheaf.map_id _
  exact Subsingleton.elim _ _
theorem comp_eq_SpecMap_iff {L : Type} [Field L] [Algebra k L] (x : X)
    (ψ : X.residueField x ⟶ CommRingCat.of L) :
    (Spec.map ψ ≫ X.fromSpecResidueField x) ≫ f = Spec.map (CommRingCat.ofHom (algebraMap k L)) ↔
      residueStructure f x ≫ ψ = CommRingCat.ofHom (algebraMap k L) := by
  have key : ∀ g₁ g₂ : Spec (.of L) ⟶ Spec (.of k), g₁ = g₂ ↔
      (Scheme.ΓSpecIso (.of k)).inv ≫ g₁.appTop ≫ (Scheme.ΓSpecIso (.of L)).hom =
        (Scheme.ΓSpecIso (.of k)).inv ≫ g₂.appTop ≫ (Scheme.ΓSpecIso (.of L)).hom := by
    intro g₁ g₂
    refine ⟨fun h ↦ h ▸ rfl, fun h ↦ ext_of_isAffine ?_⟩
    rwa [cancel_epi, cancel_mono] at h
  rw [key]
  simp only [Scheme.Hom.comp_appTop, Category.assoc, Scheme.ΓSpecIso_naturality,
    Iso.inv_hom_id_assoc, fromSpecResidueField_appTop_assoc, residueStructure]
noncomputable def residueHomEquiv {L : Type} [Field L] [Algebra k L] (x : X) :
    {ψ : X.residueField x ⟶ CommRingCat.of L //
        residueStructure f x ≫ ψ = CommRingCat.ofHom (algebraMap k L)} ≃
      (letI := residueAlgebra f x; X.residueField x →ₐ[k] L) :=
  letI := residueAlgebra f x
  { toFun := fun ψ ↦
      { ψ.1.hom with
        commutes' := fun r ↦ by
          have := congrArg (fun g ↦ g.hom r) ψ.2
          simpa [RingHom.algebraMap_toAlgebra] using this }
    invFun := fun φ ↦ ⟨CommRingCat.ofHom φ.toRingHom, by
      ext r
      change φ ((residueStructure f x).hom r) = algebraMap k L r
      exact φ.commutes r⟩
    left_inv := fun _ ↦ rfl
    right_inv := fun _ ↦ rfl }
def sigmaSubtypeEquiv {α : Type*} {β : α → Type*} (P : ∀ a, β a → Prop) :
    {σ : Σ a, β a // P σ.1 σ.2} ≃ Σ a, {b : β a // P a b} where
  toFun σ := ⟨σ.1.1, σ.1.2, σ.2⟩
  invFun σ := ⟨⟨σ.1, σ.2.1⟩, σ.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
noncomputable def pointsOverEquiv (L : Type) [Field L] [Algebra k L] :
    {g : Spec (.of L) ⟶ X // g ≫ f = Spec.map (CommRingCat.ofHom (algebraMap k L))} ≃
      Σ x : X, (letI := residueAlgebra f x; X.residueField x →ₐ[k] L) :=
  ((Equiv.subtypeEquiv (Scheme.SpecToEquivOfField L X) fun g ↦ by
      conv_lhs => rw [← (Scheme.SpecToEquivOfField L X).symm_apply_apply g]
      exact comp_eq_SpecMap_iff f _ _).trans
    (sigmaSubtypeEquiv fun x ψ ↦
      residueStructure f x ≫ ψ = CommRingCat.ofHom (algebraMap k L))).trans
    (Equiv.sigmaCongrRight fun x ↦ residueHomEquiv f x)
theorem natCard_algHom_extension (p : ℕ) [Fact p.Prime] {k : Type} [Field k] [Finite k]
    [CharP k p] (E : Type*) [Field E] [Algebra k E] (m : ℕ) [NeZero m] :
    Nat.card (E →ₐ[k] FiniteField.Extension k p m) =
      if Module.finrank k E ∣ m then Module.finrank k E else 0 := by
  have hL := FiniteField.finrank_extension k p m
  split_ifs with h
  · exact FiniteField.natCard_algHom_of_finrank_dvd (by rw [hL]; exact h)
  · have : IsEmpty (E →ₐ[k] FiniteField.Extension k p m) := by
      rw [← not_nonempty_iff, FiniteField.nonempty_algHom_iff_finrank_dvd, hL]
      exact h
    exact Nat.card_of_isEmpty
theorem pointCount_eq_natCard_sigma (p : ℕ) [Fact p.Prime] [Finite k] [CharP k p] (m : ℕ)
    [NeZero m] :
    pointCount p f m = Nat.card (Σ x : X, (letI := residueAlgebra f x;
      X.residueField x →ₐ[k] FiniteField.Extension k p m)) := by
  rw [pointCount_of_neZero, pointsOver]
  exact Nat.card_congr (pointsOverEquiv f _)
end WeilConjectures.Bridge
end
section
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicGeometry CategoryTheory
namespace WeilConjectures.Bridge
variable {k : Type} [Field k] {X : Scheme.{0}} (f : X ⟶ Spec (.of k))
noncomputable def residueDegree (x : X) : ℕ :=
  letI := residueAlgebra f x
  Module.finrank k (X.residueField x)
variable (p : ℕ) [Fact p.Prime] [Finite k] [CharP k p]
abbrev ResiduePoints (m : ℕ) [NeZero m] : Type :=
  Σ x : X, (letI := residueAlgebra f x; X.residueField x →ₐ[k] FiniteField.Extension k p m)
theorem finite_residuePoints [LocallyOfFiniteType f] [QuasiCompact f] (m : ℕ) [NeZero m] :
    Finite (ResiduePoints f p m) := by
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, (Nat.succ_pred_eq_of_pos (NeZero.pos m)).symm⟩
  have : Finite (FiniteFields.ExtensionPoint (k := k) (p := p) X f n) := inferInstance
  exact Finite.of_equiv _ ((rationalPointEquiv f _).trans (pointsOverEquiv f _))
include p in
theorem finite_residueDegree_eq [LocallyOfFiniteType f] [QuasiCompact f] {d : ℕ} (hd : 0 < d) :
    Finite {x : X // residueDegree f x = d} := by
  have : NeZero d := ⟨hd.ne'⟩
  have := finite_residuePoints f p d
  have hne : ∀ x : {x : X // residueDegree f x = d},
      Nonempty (letI := residueAlgebra f x.1;
        X.residueField x.1 →ₐ[k] FiniteField.Extension k p d) := fun x ↦ by
    let := residueAlgebra f x.1
    rw [FiniteField.nonempty_algHom_iff_finrank_dvd, FiniteField.finrank_extension]
    have h := x.2
    unfold residueDegree at h
    rw [h]
  refine Finite.of_injective (fun x ↦ (⟨x.1, (hne x).some⟩ : ResiduePoints f p d)) ?_
  intro x y h
  exact Subtype.ext (congrArg Sigma.fst h)
theorem pointCount_eq_sum_residueDegree [LocallyOfFiniteType f] [QuasiCompact f] (m : ℕ)
    [NeZero m] :
    pointCount p f m = ∑ d ∈ m.divisors, d * Nat.card {x : X // residueDegree f x = d} := by
  classical
  have hm : m ≠ 0 := NeZero.ne m
  have hfin : Set.Finite {x : X | residueDegree f x ∣ m ∧ 0 < residueDegree f x} := by
    have : {x : X | residueDegree f x ∣ m ∧ 0 < residueDegree f x} =
        ⋃ d ∈ m.divisors, {x : X | residueDegree f x = d} := by
      ext x
      simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Nat.mem_divisors, exists_prop]
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨_, ⟨h1, hm⟩, rfl⟩
      · rintro ⟨d, ⟨h1, -⟩, rfl⟩
        exact ⟨h1, Nat.pos_of_dvd_of_pos h1 (Nat.pos_of_ne_zero hm)⟩
    rw [this]
    refine Set.Finite.biUnion (Finset.finite_toSet _) fun d hd ↦ ?_
    exact Set.finite_coe_iff.mp (finite_residueDegree_eq f p (Nat.pos_of_mem_divisors hd))
  set T := hfin.toFinset
  have hcard : ∀ x : X, Nat.card (letI := residueAlgebra f x;
      X.residueField x →ₐ[k] FiniteField.Extension k p m) =
        if x ∈ T then residueDegree f x else 0 := by
    intro x
    let := residueAlgebra f x
    rw [natCard_algHom_extension p (X.residueField x) m]
    simp only [T, Set.Finite.mem_toFinset, Set.mem_ofPred_eq, residueDegree]
    by_cases h1 : Module.finrank k (X.residueField x) ∣ m
    · by_cases h2 : 0 < Module.finrank k (X.residueField x)
      · simp [h1, h2]
      · have : Module.finrank k (X.residueField x) = 0 := by omega
        simp [h1, this]
    · simp [h1]
  rw [pointCount_eq_natCard_sigma f p m]
  have hempty : ∀ x : X, x ∉ T → IsEmpty (letI := residueAlgebra f x;
      X.residueField x →ₐ[k] FiniteField.Extension k p m) := fun x hx ↦ by
    let := residueAlgebra f x
    have h := hcard x
    rw [if_neg hx] at h
    have : Finite (X.residueField x →ₐ[k] FiniteField.Extension k p m) := by
      have := finite_residuePoints f p m
      exact Finite.of_injective (fun φ ↦ (⟨x, φ⟩ : ResiduePoints f p m))
        fun a b hab ↦ eq_of_heq (Sigma.mk.inj_iff.mp hab).2
    exact (Nat.card_eq_zero.mp h).resolve_right (not_infinite_iff_finite.mpr this)
  let e : ResiduePoints f p m ≃ Σ x : T, (letI := residueAlgebra f x.1;
      X.residueField x.1 →ₐ[k] FiniteField.Extension k p m) :=
    { toFun := fun σ ↦ ⟨⟨σ.1, by
          by_contra hx
          exact (hempty σ.1 hx).false σ.2⟩, σ.2⟩
      invFun := fun σ ↦ ⟨σ.1.1, σ.2⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }
  have hfinfib : ∀ x : T, Finite (letI := residueAlgebra f x.1;
      X.residueField x.1 →ₐ[k] FiniteField.Extension k p m) := fun x ↦ by
    have := finite_residuePoints f p m
    exact Finite.of_injective (fun φ ↦ (⟨x.1, φ⟩ : ResiduePoints f p m))
      fun a b hab ↦ eq_of_heq (Sigma.mk.inj_iff.mp hab).2
  rw [Nat.card_congr e, Nat.card_sigma]
  simp only [hcard, Finset.coe_mem, if_true]
  rw [Finset.sum_coe_sort T (residueDegree f)]
  rw [← Finset.sum_fiberwise_of_maps_to (g := residueDegree f) (t := m.divisors)]
  · refine Finset.sum_congr rfl fun d hd ↦ ?_
    rw [Finset.sum_congr rfl fun x hx ↦ (Finset.mem_filter.mp hx).2, Finset.sum_const,
      smul_eq_mul, mul_comm]
    congr 1
    have := finite_residueDegree_eq f p (Nat.pos_of_mem_divisors hd)
    rw [← Nat.card_eq_finsetCard]
    refine Nat.card_congr (Equiv.subtypeEquivRight fun x ↦ ?_)
    simp only [Finset.mem_filter, T, Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨-, h⟩
      exact h
    · intro h
      exact ⟨⟨h ▸ Nat.dvd_of_mem_divisors hd, h ▸ Nat.pos_of_mem_divisors hd⟩, h⟩
  · intro x hx
    simp only [T, Set.Finite.mem_toFinset, Set.mem_ofPred_eq] at hx
    exact Nat.mem_divisors.mpr ⟨hx.1, hm⟩
end WeilConjectures.Bridge
end
section
noncomputable section
open PowerSeries FiniteFields.Dwork
namespace WeilConjectures.Bridge
section Generic
variable (a : ℕ → ℕ)
def eulerCounts (m : ℕ) : ℕ := ∑ d ∈ m.divisors, d * a d
def eulerPartial (R : Type*) [CommRing R] (M : ℕ) : PowerSeries R :=
  ∏ e ∈ Finset.Icc 1 M, (geomFactor R e) ^ (a e)
def eulerLogDeriv' (M : ℕ) : ℚ⟦X⟧ :=
  ∑ e ∈ Finset.Icc 1 M, (a e : ℚ⟦X⟧) * (e : ℚ⟦X⟧) * X ^ (e - 1) * geomFactor ℚ e
theorem map_eulerPartial (M : ℕ) :
    PowerSeries.map (Int.castRingHom ℚ) (eulerPartial a ℤ M) = eulerPartial a ℚ M := by
  rw [eulerPartial, eulerPartial, map_prod]
  exact Finset.prod_congr rfl fun e _ ↦ by rw [map_pow, map_geomFactor]
theorem constantCoeff_eulerPartial (M : ℕ) : constantCoeff (eulerPartial a ℚ M) = 1 := by
  rw [eulerPartial, map_prod]
  refine Finset.prod_eq_one fun e _ ↦ ?_
  rw [map_pow, ← coeff_zero_eq_constantCoeff, coeff_geomFactor, if_pos (dvd_zero e), one_pow]
theorem derivative_geomFactor_pow' (e c : ℕ) (he : 0 < e) :
    d⁄dX ℚ ((geomFactor ℚ e) ^ c) =
      (c : ℚ⟦X⟧) * (e : ℚ⟦X⟧) * X ^ (e - 1) * geomFactor ℚ e * (geomFactor ℚ e) ^ c := by
  induction c with
  | zero => simp
  | succ c ih =>
    rw [pow_succ, Derivation.leibniz, ih, derivative_geomFactor e he]
    simp only [smul_eq_mul]
    push_cast
    ring
theorem derivative_prod_geomFactor (s : Finset ℕ) (hs : ∀ e ∈ s, 0 < e) :
    d⁄dX ℚ (∏ e ∈ s, (geomFactor ℚ e) ^ (a e)) =
      (∑ e ∈ s, (a e : ℚ⟦X⟧) * (e : ℚ⟦X⟧) * X ^ (e - 1) * geomFactor ℚ e) *
        ∏ e ∈ s, (geomFactor ℚ e) ^ (a e) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert b t hb ih =>
    have hpos : 0 < b := hs b (Finset.mem_insert_self b t)
    rw [Finset.prod_insert hb, Finset.sum_insert hb, Derivation.leibniz,
      ih fun e he ↦ hs e (Finset.mem_insert_of_mem he), derivative_geomFactor_pow' b _ hpos]
    simp only [smul_eq_mul]
    ring
theorem derivative_eulerPartial (M : ℕ) :
    d⁄dX ℚ (eulerPartial a ℚ M) = eulerLogDeriv' a M * eulerPartial a ℚ M :=
  derivative_prod_geomFactor a _ fun _ he ↦ (Finset.mem_Icc.mp he).1
theorem coeff_eulerLogDeriv' (M j : ℕ) (hj : j + 1 ≤ M) :
    coeff j (eulerLogDeriv' a M) = (eulerCounts a (j + 1) : ℚ) := by
  classical
  have hterm : ∀ e ∈ Finset.Icc 1 M,
      coeff j ((a e : ℚ⟦X⟧) * (e : ℚ⟦X⟧) * X ^ (e - 1) * geomFactor ℚ e) =
        if e ∈ (j + 1).divisors then ((e * a e : ℕ) : ℚ) else 0 := by
    intro e he
    obtain ⟨he1, _⟩ := Finset.mem_Icc.mp he
    have hrw : (a e : ℚ⟦X⟧) * (e : ℚ⟦X⟧) * X ^ (e - 1) * geomFactor ℚ e =
        C ((e * a e : ℕ) : ℚ) * (X ^ (e - 1) * geomFactor ℚ e) := by
      rw [map_natCast]
      push_cast
      ring
    rw [hrw, coeff_C_mul, coeff_X_pow_mul']
    by_cases hle : e - 1 ≤ j
    · rw [if_pos hle, coeff_geomFactor]
      have hdvdiff : e ∣ j - (e - 1) ↔ e ∣ j + 1 := by
        have hsub : j - (e - 1) + e = j + 1 := by omega
        constructor
        · intro hd
          have := Nat.dvd_add hd (dvd_refl e)
          rwa [hsub] at this
        · intro hd
          have := Nat.dvd_sub hd (dvd_refl e)
          rwa [show j + 1 - e = j - (e - 1) by omega] at this
      by_cases hd : e ∣ j + 1
      · rw [if_pos (hdvdiff.mpr hd), if_pos (Nat.mem_divisors.mpr ⟨hd, Nat.succ_ne_zero j⟩),
          mul_one]
      · rw [if_neg (fun hc ↦ hd (hdvdiff.mp hc)), mul_zero,
          if_neg (fun hc ↦ hd (Nat.mem_divisors.mp hc).1)]
    · rw [if_neg hle, mul_zero, if_neg]
      intro hc
      exact hle (by
        have := Nat.le_of_dvd (Nat.succ_pos j) (Nat.mem_divisors.mp hc).1
        omega)
  rw [eulerLogDeriv', map_sum, Finset.sum_congr rfl hterm, Finset.sum_ite_mem]
  have hsubset : (j + 1).divisors ∩ Finset.Icc 1 M = (j + 1).divisors := by
    refine Finset.inter_eq_left.mpr fun e he ↦ ?_
    obtain ⟨hd, _⟩ := Nat.mem_divisors.mp he
    have hle := Nat.le_of_dvd (Nat.succ_pos j) hd
    exact Finset.mem_Icc.mpr ⟨Nat.pos_of_dvd_of_pos hd (Nat.succ_pos j), by omega⟩
  rw [Finset.inter_comm, hsubset, eulerCounts]
  push_cast
  rfl
theorem coeff_eulerPartial_eq (M : ℕ) :
    ∀ m ≤ M, coeff m (eulerPartial a ℚ M) = coeff m (zetaOfCounts (eulerCounts a)) := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro hm
    cases m with
    | zero =>
      rw [coeff_zero_eq_constantCoeff_apply, coeff_zero_eq_constantCoeff_apply,
        constantCoeff_eulerPartial, constantCoeff_zetaOfCounts]
    | succ m =>
      have hW := congrArg (coeff m) (derivative_eulerPartial a M)
      have hZ := congrArg (coeff m) (derivative_zetaOfCounts (eulerCounts a))
      rw [coeff_derivative, coeff_mul] at hW hZ
      have hsum : ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal m,
          coeff ij.1 (eulerLogDeriv' a M) * coeff ij.2 (eulerPartial a ℚ M) =
            ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal m,
              coeff ij.1 (countingSeries (eulerCounts a)) *
                coeff ij.2 (zetaOfCounts (eulerCounts a)) := by
        refine Finset.sum_congr rfl fun ij hij ↦ ?_
        have hij' : ij.1 + ij.2 = m := Finset.HasAntidiagonal.mem_antidiagonal.mp hij
        rw [coeff_eulerLogDeriv' a M ij.1 (by omega), ih ij.2 (by omega) (by omega),
          coeff_countingSeries]
      rw [hsum] at hW
      have hne : ((m : ℚ) + 1) ≠ 0 := by positivity
      apply mul_right_cancel₀ hne
      rw [hW, hZ]
theorem zetaOfCounts_eulerCounts_integral :
    ∃ Z : PowerSeries ℤ, constantCoeff Z = 1 ∧
      PowerSeries.map (Int.castRingHom ℚ) Z = zetaOfCounts (eulerCounts a) := by
  refine ⟨PowerSeries.mk fun m ↦ coeff m (eulerPartial a ℤ m), ?_, ?_⟩
  · have := constantCoeff_eulerPartial a 0
    rw [← map_eulerPartial, ← coeff_zero_eq_constantCoeff_apply, coeff_map] at this
    rw [← coeff_zero_eq_constantCoeff_apply, coeff_mk]
    rw [eq_intCast] at this
    exact_mod_cast this
  · ext m
    rw [coeff_map, coeff_mk, ← coeff_eulerPartial_eq a m m le_rfl, ← map_eulerPartial, coeff_map]
end Generic
variable {k : Type} [Field k] {X : AlgebraicGeometry.Scheme.{0}}
  (f : X ⟶ AlgebraicGeometry.Spec (.of k)) (p : ℕ) [Fact p.Prime] [Finite k] [CharP k p]
theorem zetaFunction_integral [AlgebraicGeometry.LocallyOfFiniteType f]
    [AlgebraicGeometry.QuasiCompact f] :
    ∃ Z : PowerSeries ℤ, constantCoeff Z = 1 ∧
      PowerSeries.map (Int.castRingHom ℚ) Z = zetaFunction p f := by
  obtain ⟨Z, h0, hZ⟩ := zetaOfCounts_eulerCounts_integral
    (fun d ↦ Nat.card {x : X // residueDegree f x = d})
  refine ⟨Z, h0, hZ.trans ?_⟩
  rw [zetaFunction]
  refine zetaOfCounts_congr fun m hm ↦ ?_
  have : NeZero m := ⟨by omega⟩
  rw [pointCount_eq_sum_residueDegree f p m]
  rfl
end WeilConjectures.Bridge
end
end
section
open Polynomial
namespace WeilConjectures.Bridge
section Fatou
theorem coe_polynomial_map {R S : Type*} [CommSemiring R] [CommSemiring S] (f : R →+* S)
    (A : R[X]) : ((A.map f : S[X]) : PowerSeries S) = PowerSeries.map f (A : PowerSeries R) := by
  ext k
  simp [Polynomial.coeff_coe, coeff_map]
theorem exists_int_mul_eq_map (U : ℚ[X]) :
    ∃ b : ℤ, b ≠ 0 ∧ ∃ U' : ℤ[X], U'.map (Int.castRingHom ℚ) = C (b : ℚ) * U := by
  obtain ⟨b, hb, h⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors ℤ) U
  refine ⟨b, nonZeroDivisors.ne_zero hb, IsLocalization.integerNormalization (nonZeroDivisors ℤ) U, ?_⟩
  rw [← algebraMap_int_eq, h, zsmul_eq_mul, ← C_eq_intCast]
theorem isUnit_coeff_zero_of_mul_eq_C {Q₀ : ℤ[X]} (hQ₀ : Q₀.IsPrimitive) :
    ∀ (N : ℕ) (R : PowerSeries ℤ) (c : ℤ), c.natAbs = N → c ≠ 0 →
      (Q₀ : PowerSeries ℤ) * R = PowerSeries.C c → IsUnit (Q₀.coeff 0) := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
  intro R c hN hc hQR
  by_cases h1 : c.natAbs = 1
  · have h := congrArg PowerSeries.constantCoeff hQR
    rw [map_mul, PowerSeries.constantCoeff_C, ← PowerSeries.coeff_zero_eq_constantCoeff_apply,
      Polynomial.coeff_coe] at h
    exact isUnit_of_mul_isUnit_left (h ▸ Int.isUnit_iff_natAbs_eq.mpr h1)
  ·
    obtain ⟨ℓ, hℓ, hℓc⟩ := Nat.exists_prime_and_dvd h1
    have := Fact.mk hℓ
    have hℓc' : (ℓ : ℤ) ∣ c := Int.natCast_dvd.mpr hℓc
    let φ := PowerSeries.map (Int.castRingHom (ZMod ℓ))
    have hφ : φ (Q₀ : PowerSeries ℤ) * φ R = 0 := by
      rw [← map_mul, hQR, PowerSeries.map_C, eq_intCast,
        (ZMod.intCast_zmod_eq_zero_iff_dvd c ℓ).mpr hℓc', map_zero]
    have hQ₀ℓ : φ (Q₀ : PowerSeries ℤ) ≠ 0 := by
      intro h0
      have hdvd : C (ℓ : ℤ) ∣ Q₀ := by
        rw [C_dvd_iff_dvd_coeff]
        intro i
        have := congrArg (PowerSeries.coeff i) h0
        rw [PowerSeries.coeff_map, Polynomial.coeff_coe, map_zero, eq_intCast] at this
        exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ ℓ).mp this
      exact (Nat.prime_iff_prime_int.mp hℓ).not_unit (hQ₀ _ hdvd)
    have hR0 : φ R = 0 := (mul_eq_zero.mp hφ).resolve_left hQ₀ℓ
    have hdivR : ∀ k, (ℓ : ℤ) ∣ PowerSeries.coeff k R := fun k ↦ by
      have := congrArg (PowerSeries.coeff k) hR0
      rw [PowerSeries.coeff_map, map_zero, eq_intCast] at this
      exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ ℓ).mp this
    set R₁ : PowerSeries ℤ := PowerSeries.mk fun k ↦ PowerSeries.coeff k R / ℓ
    have hRR₁ : R = PowerSeries.C (ℓ : ℤ) * R₁ := by
      ext k
      rw [PowerSeries.coeff_C_mul, PowerSeries.coeff_mk, Int.mul_ediv_cancel' (hdivR k)]
    have hℓ0 : (PowerSeries.C (ℓ : ℤ) : PowerSeries ℤ) ≠ 0 := by
      intro h
      have := congrArg PowerSeries.constantCoeff h
      rw [PowerSeries.constantCoeff_C, map_zero] at this
      exact hℓ.ne_zero (by exact_mod_cast this)
    have hQR₁ : (Q₀ : PowerSeries ℤ) * R₁ = PowerSeries.C (c / ℓ) := by
      refine mul_left_cancel₀ hℓ0 ?_
      rw [← map_mul, Int.mul_ediv_cancel' hℓc', ← hQR, hRR₁]
      ring
    refine ih (c / ℓ).natAbs ?_ R₁ (c / ℓ) rfl ?_ hQR₁
    · rw [← hN, Int.natAbs_ediv_of_dvd hℓc', Int.natAbs_natCast]
      exact Nat.div_lt_self (Int.natAbs_pos.mpr hc) hℓ.one_lt
    · exact fun h ↦ hc (by rw [← Int.mul_ediv_cancel' hℓc', h, mul_zero])
theorem isUnit_coeff_zero_of_mul_eq_C' {Q₀ : ℤ[X]} (hQ₀ : Q₀.IsPrimitive) {R : PowerSeries ℤ}
    {c : ℤ} (hc : c ≠ 0) (h : (Q₀ : PowerSeries ℤ) * R = PowerSeries.C c) : IsUnit (Q₀.coeff 0) :=
  isUnit_coeff_zero_of_mul_eq_C hQ₀ _ R c rfl hc h
theorem eq_C_of_C_mul_eq_C {W : PowerSeries ℤ} {d e : ℤ} (hd : d ≠ 0)
    (h : PowerSeries.C d * W = PowerSeries.C e) : W = PowerSeries.C (PowerSeries.constantCoeff W) := by
  ext k
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp
  · have := congrArg (PowerSeries.coeff k) h
    rw [PowerSeries.coeff_C_mul, PowerSeries.coeff_C, if_neg hk.ne'] at this
    rw [PowerSeries.coeff_C, if_neg hk.ne']
    exact (mul_eq_zero.mp this).resolve_left hd
theorem fatou {F : PowerSeries ℤ} {P Q : ℚ[X]} (hQ0 : Q.coeff 0 = 1) (hcop : IsCoprime P Q)
    (h : PowerSeries.map (Int.castRingHom ℚ) F * (Q : PowerSeries ℚ) = (P : PowerSeries ℚ)) :
    ∃ A B : ℤ[X], A.map (Int.castRingHom ℚ) = P ∧ B.map (Int.castRingHom ℚ) = Q := by
  set ι := PowerSeries.map (Int.castRingHom ℚ)
  have hι : Function.Injective ι := PowerSeries.map_injective _ (RingHom.injective_int _)
  have hcoe : ∀ A : ℤ[X], ((A.map (Int.castRingHom ℚ) : ℚ[X]) : PowerSeries ℚ) = ι A :=
    fun A ↦ coe_polynomial_map _ A
  have hιC : ∀ z : ℤ, ι (PowerSeries.C z) = PowerSeries.C (z : ℚ) := fun z ↦ by
    simp [ι, PowerSeries.map_C]
  obtain ⟨U, V, hUV⟩ := hcop
  have hQG : (Q : PowerSeries ℚ) * ((U : PowerSeries ℚ) * ι F + (V : PowerSeries ℚ)) = 1 := by
    have h1 : ((U * P + V * Q : ℚ[X]) : PowerSeries ℚ) = 1 := by rw [hUV, Polynomial.coe_one]
    rw [Polynomial.coe_add, Polynomial.coe_mul, Polynomial.coe_mul, ← h] at h1
    rw [← h1]
    ring
  obtain ⟨bU, hbU, U', hU'⟩ := exists_int_mul_eq_map U
  obtain ⟨bV, hbV, V', hV'⟩ := exists_int_mul_eq_map V
  obtain ⟨bQ, hbQ, Q₁, hQ₁⟩ := exists_int_mul_eq_map Q
  set R : PowerSeries ℤ := ((C bV * U' : ℤ[X]) : PowerSeries ℤ) * F + ((C bU * V' : ℤ[X]) : PowerSeries ℤ)
  have hR : ι R = PowerSeries.C ((bU * bV : ℤ) : ℚ) *
      ((U : PowerSeries ℚ) * ι F + (V : PowerSeries ℚ)) := by
    have e1 : ι ((C bV * U' : ℤ[X]) : PowerSeries ℤ) =
        PowerSeries.C (bV : ℚ) * (PowerSeries.C (bU : ℚ) * (U : PowerSeries ℚ)) := by
      rw [← hcoe, Polynomial.map_mul, hU', Polynomial.map_C, eq_intCast, Polynomial.coe_mul,
        Polynomial.coe_mul, Polynomial.coe_C, Polynomial.coe_C]
    have e2 : ι ((C bU * V' : ℤ[X]) : PowerSeries ℤ) =
        PowerSeries.C (bU : ℚ) * (PowerSeries.C (bV : ℚ) * (V : PowerSeries ℚ)) := by
      rw [← hcoe, Polynomial.map_mul, hV', Polynomial.map_C, eq_intCast, Polynomial.coe_mul,
        Polynomial.coe_mul, Polynomial.coe_C, Polynomial.coe_C]
    simp only [R, map_add, map_mul]
    rw [e1, e2, Int.cast_mul, map_mul]
    ring
  have hQ₁0 : Q₁ ≠ 0 := by
    rintro rfl
    rw [Polynomial.map_zero] at hQ₁
    have := congrArg (coeff · 0) hQ₁
    simp [coeff_C_mul, hQ0] at this
    exact hbQ (by exact_mod_cast this.symm)
  set d := Q₁.content
  set Q₀ := Q₁.primPart
  have hd : d ≠ 0 := fun h0 ↦ hQ₁0 (content_eq_zero_iff.mp h0)
  have hQ₁d : Q₁ = C d * Q₀ := eq_C_content_mul_primPart Q₁
  have hmain : PowerSeries.C d * ((Q₀ : PowerSeries ℤ) * R) = PowerSeries.C (bQ * (bU * bV)) := by
    refine hι ?_
    have e : ι ((C d * Q₀ : ℤ[X]) : PowerSeries ℤ) = PowerSeries.C (bQ : ℚ) * (Q : PowerSeries ℚ) := by
      rw [← hQ₁d, ← hcoe, hQ₁, Polynomial.coe_mul, Polynomial.coe_C]
    calc ι (PowerSeries.C d * ((Q₀ : PowerSeries ℤ) * R))
        = ι ((C d * Q₀ : ℤ[X]) : PowerSeries ℤ) * ι R := by
          rw [Polynomial.coe_mul, Polynomial.coe_C, ← map_mul, mul_assoc]
      _ = PowerSeries.C (bQ : ℚ) * PowerSeries.C ((bU * bV : ℤ) : ℚ) *
            ((Q : PowerSeries ℚ) * ((U : PowerSeries ℚ) * ι F + (V : PowerSeries ℚ))) := by
          rw [e, hR]
          ring
      _ = ι (PowerSeries.C (bQ * (bU * bV))) := by
          rw [hQG, mul_one, hιC, ← map_mul]
          push_cast
          rfl
  have hW := eq_C_of_C_mul_eq_C hd hmain
  have hc0 : PowerSeries.constantCoeff ((Q₀ : PowerSeries ℤ) * R) ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hW
    rw [hW, mul_zero] at hmain
    have := congrArg PowerSeries.constantCoeff hmain
    rw [map_zero, PowerSeries.constantCoeff_C] at this
    exact mul_ne_zero hbQ (mul_ne_zero hbU hbV) this.symm
  have hu := isUnit_coeff_zero_of_mul_eq_C' (isPrimitive_primPart Q₁) hc0 hW
  set u := Q₀.coeff 0
  have hu2 : u * u = 1 := by
    rcases Int.isUnit_iff.mp hu with h1 | h1 <;> rw [h1] <;> norm_num
  have hbQd : (bQ : ℚ) = d * u := by
    have := congrArg (coeff · 0) hQ₁
    simp only [coeff_map, coeff_C_mul, hQ0, mul_one, eq_intCast] at this
    rw [← this, hQ₁d, coeff_C_mul]
    push_cast
    rfl
  have hB : (C u * Q₀).map (Int.castRingHom ℚ) = Q := by
    have h1 : C (d : ℚ) * Q₀.map (Int.castRingHom ℚ) = C (d : ℚ) * (C (u : ℚ) * Q) := by
      have := hQ₁
      rw [hQ₁d, Polynomial.map_mul, Polynomial.map_C, eq_intCast, hbQd, C_mul, mul_assoc] at this
      exact this
    have hdC : (C (d : ℚ) : ℚ[X]) ≠ 0 := C_ne_zero.mpr (Int.cast_ne_zero.mpr hd)
    rw [Polynomial.map_mul, Polynomial.map_C, eq_intCast, mul_left_cancel₀ hdC h1, ← mul_assoc,
      ← C_mul, ← Int.cast_mul, hu2, Int.cast_one, C_1, one_mul]
  have hG : ι (F * ((C u * Q₀ : ℤ[X]) : PowerSeries ℤ)) = (P : PowerSeries ℚ) := by
    rw [map_mul, ← hcoe, hB, h]
  refine ⟨PowerSeries.trunc (P.natDegree + 1) (F * ((C u * Q₀ : ℤ[X]) : PowerSeries ℤ)),
    C u * Q₀, ?_, hB⟩
  ext k
  rw [coeff_map, PowerSeries.coeff_trunc]
  split_ifs with hk
  · have := congrArg (PowerSeries.coeff k) hG
    rw [PowerSeries.coeff_map, Polynomial.coeff_coe] at this
    simpa using this
  · rw [map_zero]
    exact (coeff_eq_zero_of_natDegree_lt (by omega)).symm
end Fatou
end WeilConjectures.Bridge
end
section
open AlgebraicGeometry CategoryTheory
namespace WeilConjectures.Bridge
variable {k : Type} [Field k] {X : Scheme.{0}} (f : X ⟶ Spec (.of k))
  (p : ℕ) [Fact p.Prime] [Finite k] [CharP k p]
theorem zetaFunction_integral_presentation_of_finiteType
    (hf : FiniteFields.Schemes.FiniteType f) (hsep : IsSeparated f) :
    ∃ A B : Polynomial ℤ, A.coeff 0 = 1 ∧ B.coeff 0 = 1 ∧
      IsCoprime (A.map (Int.castRingHom ℚ)) (B.map (Int.castRingHom ℚ)) ∧
      zetaFunction p f * ((B.map (Int.castRingHom ℚ) : Polynomial ℚ) : PowerSeries ℚ) =
        ((A.map (Int.castRingHom ℚ) : Polynomial ℚ) : PowerSeries ℚ) := by
  obtain ⟨P, Q, hQ, hcop, -, hPQ⟩ := FiniteFields.dwork_rationality_explicit k p f hf hsep
  have : LocallyOfFiniteType f := hf.1
  have : QuasiCompact f := hf.2
  obtain ⟨Zℤ, hZ0, hZ⟩ := zetaFunction_integral f p
  have hZeq := zetaFunction_eq_zetaSeriesOf f p hf
  have hF : PowerSeries.map (Int.castRingHom ℚ) Zℤ * (Q : PowerSeries ℚ) = (P : PowerSeries ℚ) := by
    rw [hZ, hZeq, mul_comm]
    exact hPQ
  have hQ0 : Q.coeff 0 = 1 := by rwa [Polynomial.coeff_zero_eq_eval_zero]
  obtain ⟨A, B, hA, hB⟩ := fatou hQ0 hcop hF
  have hP0 : P.coeff 0 = 1 := by
    have := congrArg PowerSeries.constantCoeff hF
    rw [map_mul, ← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map,
      PowerSeries.coeff_zero_eq_constantCoeff_apply, hZ0, map_one, one_mul,
      ← PowerSeries.coeff_zero_eq_constantCoeff_apply, Polynomial.coeff_coe,
      ← PowerSeries.coeff_zero_eq_constantCoeff_apply, Polynomial.coeff_coe, hQ0] at this
    exact this.symm
  refine ⟨A, B, ?_, ?_, by rw [hA, hB]; exact hcop, ?_⟩
  · have := congrArg (Polynomial.coeff · 0) hA
    simp only [Polynomial.coeff_map, eq_intCast, hP0] at this
    exact_mod_cast this
  · have := congrArg (Polynomial.coeff · 0) hB
    simp only [Polynomial.coeff_map, eq_intCast, hQ0] at this
    exact_mod_cast this
  · rw [hA, hB, hZeq, mul_comm]
    exact hPQ
theorem zetaFunction_integral_presentation (hproj : IsProjectiveOver k f) :
    ∃ A B : Polynomial ℤ, A.coeff 0 = 1 ∧ B.coeff 0 = 1 ∧
      IsCoprime (A.map (Int.castRingHom ℚ)) (B.map (Int.castRingHom ℚ)) ∧
      zetaFunction p f * ((B.map (Int.castRingHom ℚ) : Polynomial ℚ) : PowerSeries ℚ) =
        ((A.map (Int.castRingHom ℚ) : Polynomial ℚ) : PowerSeries ℚ) := by
  obtain ⟨hf, hsep⟩ := finiteType_and_isSeparated_of_isProjectiveOver f hproj
  exact zetaFunction_integral_presentation_of_finiteType f p hf hsep
end WeilConjectures.Bridge
end
open AlgebraicGeometry CategoryTheory Polynomial
open WeilConjectures
theorem solution (p : ℕ) [Fact p.Prime] (k : Type)
    [Field k] [Finite k] [CharP k p] (X : Scheme.{0}) (f : X ⟶ Spec (.of k))
    (hproj : IsProjectiveOver k f) :
    ∃ A B : ℤ[X], A.coeff 0 = 1 ∧ B.coeff 0 = 1 ∧
      IsCoprime (A.map (Int.castRingHom ℚ)) (B.map (Int.castRingHom ℚ)) ∧
      zetaFunction p f * ((B.map (Int.castRingHom ℚ) : ℚ[X]) : PowerSeries ℚ) =
        ((A.map (Int.castRingHom ℚ) : ℚ[X]) : PowerSeries ℚ) :=
  WeilConjectures.Bridge.zetaFunction_integral_presentation f p hproj
