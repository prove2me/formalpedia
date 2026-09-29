-- Prove2me | solution 1 for Deformation.DieudonneModule.exists_hondaSystem_L_eq_fontaineHodge
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/4befc807-abc0-50de-a540-d6a35042cc36

import Mathlib
import Definitions.Def_Dieudonne_DatumAndHonda
import Definitions.Def_Dieudonne_WittVectorHom
import Definitions.Def_Dieudonne_WittHomColimit
import Definitions.Def_Dieudonne_FontaineHodge
import Theorems.Thm_Deformation_DieudonneModule_exists_surjective_of
import Theorems.Thm_Deformation_DieudonneModule_eq_zero_of_mem_fontaineHodge_of_verschiebung_eq_zero
import Theorems.Thm_Deformation_DieudonneModule_exists_mem_fontaineHodge_frobenius_eq_smul
import Theorems.Thm_Deformation_DieudonneModule_exists_mem_fontaineHodge_verschiebung_eq_of_frobenius_eq_zero
import Theorems.Thm_Deformation_DieudonneModule_exists_mem_fontaineHodge_add_eq_of_smul_eq_zero
import Theorems.Thm_Deformation_HondaSystem_range_sup_eq_top_of_isArtinian_of_isNoetherian
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Deformation_DieudonneModule_exists_hondaSystem_L_eq_fontaineHodge

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Function

universe u v w

namespace Deformation
p2m_export "Deformation" "HondaSystem TruncWitt.map TruncWitt.map_truncate TruncWitt.verschiebung TruncWitt.verschiebung_truncate TruncWitt.frobeniusFun TruncWitt.frobeniusFun_truncate TruncWitt.frobeniusFun_add TruncWitt.frobeniusFun_verschiebung_eq_smul wittHom mem_wittHom_iff verschiebung_mem_wittHom natCast_eq_zero_of_algebra frobeniusFun_mem_wittHom TruncWitt.shiftLE TruncWitt.shiftLE_truncate DieudonneModule DieudonneModule.of DieudonneModule.of_injective DieudonneModule.verschiebung DieudonneModule.verschiebung_of DieudonneModule.frobenius DieudonneModule.frobenius_of DieudonneModule.dieudonneDatum TruncWitt.fontaineKer fontaineHodge of_mem_fontaineHodge_iff SpecialFibre.reduction SpecialFibre.reduction_surjective SpecialFibre.ker_reduction_eq_span DieudonneModule.exists_surjective_of DieudonneModule.eq_zero_of_mem_fontaineHodge_of_verschiebung_eq_zero DieudonneModule.exists_mem_fontaineHodge_frobenius_eq_smul DieudonneModule.exists_mem_fontaineHodge_verschiebung_eq_of_frobenius_eq_zero DieudonneModule.exists_mem_fontaineHodge_add_eq_of_smul_eq_zero HondaSystem.range_sup_eq_top_of_isArtinian_of_isNoetherian"
namespace FontaineThmOne
p2m_open "Deformation"

section WittModule

variable (p : ℕ) [hp : Fact p.Prime] (k : Type u) [CommRing k] [CharP k p] [PerfectRing k p]
variable (A : Type v) [CommRing A] [Algebra k A]

noncomputable def φ (N : ℕ) : WittVector p k →+* TruncatedWittVector p N A :=
  (WittVector.truncate N).comp (WittVector.map (algebraMap k A))

theorem φ_apply (N : ℕ) (a : WittVector p k) :
    φ p k A N a = WittVector.truncate N (WittVector.map (algebraMap k A) a) := rfl

@[reducible] noncomputable def wittModule (N : ℕ) : Module (WittVector p k) (TruncatedWittVector p N A) :=
  Module.compHom _ (φ p k A N)

attribute [local instance] wittModule

private theorem _root_.Deformation.FontaineThmOne.smul_def (N : ℕ) (a : WittVector p k) (y : TruncatedWittVector p N A) :
    a • y = φ p k A N a * y := rfl

p2m_export "Deformation.FontaineThmOne" "smul_def"

theorem frobeniusEquiv_symm_iterate_pow (j : ℕ) (a : k) :
    ((frobeniusEquiv k p).symm^[j] a) ^ p ^ j = a := by
  induction j generalizing a with
  | zero => simp
  | succ j ih =>
    rw [Function.iterate_succ_apply, pow_succ, pow_mul, ih]
    have h := (frobeniusEquiv k p).apply_symm_apply a
    rwa [frobeniusEquiv_apply] at h

set_option linter.unusedVariables false in

def Twist (p : ℕ) (k : Type u) (A : Type v) (N : ℕ) : Type v := A

noncomputable scoped instance (N : ℕ) : CommRing (Twist p k A N) := inferInstanceAs (CommRing A)

noncomputable def ψ (N : ℕ) : WittVector p k →+* A :=
  (algebraMap k A).comp ((iterateFrobenius k p N).comp WittVector.constantCoeff)

theorem ψ_apply (N : ℕ) (a : WittVector p k) : ψ p k A N a = algebraMap k A ((a.coeff 0) ^ p ^ N) := by
  simp [ψ, iterateFrobenius_def, WittVector.constantCoeff_apply]

noncomputable scoped instance twistModule (N : ℕ) : Module (WittVector p k) (Twist p k A N) :=
  Module.compHom A (ψ p k A N)

theorem twist_smul_def (N : ℕ) (a : WittVector p k) (t : Twist p k A N) :
    a • t = (ψ p k A N a * (show A from t) : A) := rfl

noncomputable def twistEmb (N : ℕ) :
    Submodule (WittVector p k) (Twist p k A N) ↪o Submodule k A :=
  OrderEmbedding.ofMapLEIff
    (fun M =>
      { carrier := (M : Set (Twist p k A N))
        add_mem' := fun hx hy => M.add_mem hx hy
        zero_mem' := M.zero_mem
        smul_mem' := fun c x hx => by
          have h := M.smul_mem (WittVector.teichmuller p ((frobeniusEquiv k p).symm^[N] c)) hx
          rw [twist_smul_def, ψ_apply, WittVector.teichmuller_coeff_zero,
            frobeniusEquiv_symm_iterate_pow, ← Algebra.smul_def] at h
          exact h })
    (fun M M' => Iff.rfl)

theorem isArtinian_twist [IsArtinian k A] (N : ℕ) :
    IsArtinian (WittVector p k) (Twist p k A N) :=
  ⟨(twistEmb p k A N).wellFoundedLT.wf⟩

theorem isNoetherian_twist [IsNoetherian k A] (N : ℕ) :
    IsNoetherian (WittVector p k) (Twist p k A N) :=
  isNoetherian_mk (twistEmb p k A N).wellFoundedGT

noncomputable def truncLin (N : ℕ) :
    TruncatedWittVector p (N + 1) A →ₗ[WittVector p k] TruncatedWittVector p N A where
  toFun := TruncatedWittVector.truncate (Nat.le_succ N)
  map_add' x y := map_add _ x y
  map_smul' a y := by
    rw [smul_def, smul_def, map_mul, φ_apply, φ_apply,
      TruncatedWittVector.truncate_wittVector_truncate]
    rfl

noncomputable def lastCoord (N : ℕ) : A → TruncatedWittVector p (N + 1) A := fun t =>
  WittVector.truncate (N + 1)
    ((WittVector.verschiebung (p := p) (R := A))^[N] (WittVector.teichmuller p t))

theorem coeff_lastCoord (N : ℕ) (t : A) (i : Fin (N + 1)) :
    (lastCoord p A N t).coeff i = if (i : ℕ) = N then t else 0 := by
  rw [lastCoord, WittVector.coeff_truncate]
  split_ifs with h
  · have := WittVector.iterate_verschiebung_coeff (WittVector.teichmuller p t) N 0
    rw [zero_add] at this
    rw [h, this, WittVector.teichmuller_coeff_zero]
  · exact WittVector.iterate_verschiebung_coeff_eq_zero _ (by omega)

variable [CharP A p]

theorem φ_mul_lastCoord (N : ℕ) (a : WittVector p k) (t : A) :
    φ p k A (N + 1) a * lastCoord p A N t = lastCoord p A N (ψ p k A N a * t) := by
  rw [φ_apply, lastCoord, lastCoord, ← map_mul, mul_comm, WittVector.iterate_verschiebung_mul_left]
  refine TruncatedWittVector.ext fun i => ?_
  rw [WittVector.coeff_truncate, WittVector.coeff_truncate]
  by_cases h : (i : ℕ) = N
  · have key : ∀ X : WittVector p A,
        ((WittVector.verschiebung (p := p) (R := A))^[N] X).coeff N = X.coeff 0 := fun X => by
      have := WittVector.iterate_verschiebung_coeff X N 0
      rwa [zero_add] at this
    rw [h, key, key, WittVector.mul_coeff_zero,
      WittVector.teichmuller_coeff_zero, WittVector.teichmuller_coeff_zero,
      WittVector.iterate_frobenius_coeff, WittVector.map_coeff, ψ_apply, map_pow, mul_comm]
  · rw [WittVector.iterate_verschiebung_coeff_eq_zero _ (by omega),
      WittVector.iterate_verschiebung_coeff_eq_zero _ (by omega)]

omit [CharP A p] in
theorem lastCoord_add (N : ℕ) (s t : A) :
    lastCoord p A N (s + t) = lastCoord p A N s + lastCoord p A N t := by

  have key : ∀ u : A, lastCoord p A N u =
      TruncWitt.shiftLE (p := p) (show 1 ≤ N + 1 by omega)
        (WittVector.truncate 1 (WittVector.teichmuller p u)) := by
    intro u
    rw [TruncWitt.shiftLE_truncate, lastCoord]
    simp
  have h1 : WittVector.truncate 1 (WittVector.teichmuller p (s + t)) =
      WittVector.truncate 1 (WittVector.teichmuller p s) +
        WittVector.truncate (p := p) 1 (WittVector.teichmuller p t) := by
    rw [← map_add]
    refine TruncatedWittVector.ext fun i => ?_
    have hi : i = ⟨0, Nat.one_pos⟩ := Fin.ext (by omega)
    subst hi
    rw [WittVector.coeff_truncate, WittVector.coeff_truncate, Fin.val_mk,
      WittVector.teichmuller_coeff_zero, WittVector.add_coeff_zero,
      WittVector.teichmuller_coeff_zero, WittVector.teichmuller_coeff_zero]
  rw [key, key, key, h1, map_add]

noncomputable def lastLin (N : ℕ) :
    Twist p k A N →ₗ[WittVector p k] TruncatedWittVector p (N + 1) A where
  toFun t := lastCoord p A N t
  map_add' s t := lastCoord_add p A N s t
  map_smul' a t := by
    rw [RingHom.id_apply, smul_def, φ_mul_lastCoord]
    rfl

theorem range_lastLin_eq_ker (N : ℕ) :
    LinearMap.range (lastLin p k A N) = LinearMap.ker (truncLin p k A N) := by
  apply le_antisymm
  · rintro _ ⟨t, rfl⟩
    rw [LinearMap.mem_ker]
    refine TruncatedWittVector.ext fun i => ?_
    change ((TruncatedWittVector.truncate (Nat.le_succ N)) (lastCoord p A N t)).coeff i =
      (0 : TruncatedWittVector p N A).coeff i
    rw [TruncatedWittVector.coeff_truncate, coeff_lastCoord, if_neg, TruncatedWittVector.coeff_zero]
    simp only [Fin.val_castLE]
    exact Nat.ne_of_lt i.isLt
  · intro y hy
    rw [LinearMap.mem_ker] at hy
    refine ⟨y.coeff (Fin.last N), ?_⟩
    refine TruncatedWittVector.ext fun i => ?_
    change (lastCoord p A N (y.coeff (Fin.last N))).coeff i = y.coeff i
    rw [coeff_lastCoord]
    split_ifs with h
    · congr 1
      exact Fin.ext (by simp [h])
    · have hi : (i : ℕ) < N := by have := i.isLt; omega
      have := congrArg (TruncatedWittVector.coeff ⟨i, hi⟩) hy
      rw [TruncatedWittVector.coeff_zero] at this
      rw [← this]
      change ((TruncatedWittVector.truncate (Nat.le_succ N)) y).coeff ⟨i, hi⟩ = y.coeff i
      rw [TruncatedWittVector.coeff_truncate]
      rfl

omit [CharP A p] in
theorem subsingleton_zero : Subsingleton (TruncatedWittVector p 0 A) :=
  ⟨fun _ _ => TruncatedWittVector.ext fun i => i.elim0⟩

theorem isArtinian_and_isNoetherian [IsArtinian k A] [IsNoetherian k A] :
    ∀ N : ℕ, IsArtinian (WittVector p k) (TruncatedWittVector p N A) ∧
      IsNoetherian (WittVector p k) (TruncatedWittVector p N A) := by
  intro N
  induction N with
  | zero =>
    haveI := subsingleton_zero p A
    haveI : Finite (TruncatedWittVector p 0 A) := Finite.of_subsingleton
    exact ⟨isArtinian_of_finite, isNoetherian_of_finite _ _⟩
  | succ N ih =>
    haveI := ih.1
    haveI := ih.2
    haveI := isArtinian_twist p k A N
    haveI := isNoetherian_twist p k A N
    exact ⟨isArtinian_of_range_eq_ker (lastLin p k A N) (truncLin p k A N)
        (range_lastLin_eq_ker p k A N),
      isNoetherian_of_range_eq_ker (lastLin p k A N) (truncLin p k A N)
        (range_lastLin_eq_ker p k A N)⟩

end WittModule

section HomModule

variable (p : ℕ) [hp : Fact p.Prime] (k : Type u) [CommRing k] [CharP k p] [PerfectRing k p]
variable (A : Type v) [CommRing A] [Bialgebra k A]

attribute [local instance] wittModule

theorem map_φ {B : Type w} [CommRing B] [Algebra k B] (f : A →ₐ[k] B) (N : ℕ) (a : WittVector p k) :
    TruncWitt.map f.toRingHom (φ p k A N a) = φ p k B N a := by
  rw [φ_apply, φ_apply, TruncWitt.map_truncate]
  congr 1
  ext n
  simp only [WittVector.map_coeff]
  exact f.commutes _

noncomputable def wittHomSub (N : ℕ) : Submodule (WittVector p k) (TruncatedWittVector p N A) where
  carrier := wittHom k p N A
  add_mem' hx hy := (wittHom k p N A).add_mem hx hy
  zero_mem' := (wittHom k p N A).zero_mem
  smul_mem' a x hx := by
    change x ∈ wittHom k p N A at hx
    change a • x ∈ wittHom k p N A
    rw [mem_wittHom_iff] at hx ⊢
    rw [smul_def, map_mul, map_mul, map_mul, hx, mul_add]
    change TruncWitt.map (Bialgebra.comulAlgHom k A).toRingHom _ * _ + _ = _
    rw [map_φ, map_φ, map_φ]

theorem mem_wittHomSub_iff (N : ℕ) (x : TruncatedWittVector p N A) :
    x ∈ wittHomSub p k A N ↔ x ∈ wittHom k p N A := Iff.rfl

scoped instance isArtinian_wittHomSub [IsArtinian k A] [IsNoetherian k A] [CharP A p] (N : ℕ) :
    IsArtinian (WittVector p k) (wittHomSub p k A N) :=
  haveI := (isArtinian_and_isNoetherian p k A N).1
  inferInstance

scoped instance isNoetherian_wittHomSub [IsArtinian k A] [IsNoetherian k A] [CharP A p] (N : ℕ) :
    IsNoetherian (WittVector p k) (wittHomSub p k A N) :=
  haveI := (isArtinian_and_isNoetherian p k A N).2
  inferInstance

noncomputable abbrev σ : WittVector p k →+* WittVector p k := WittVector.frobenius

noncomputable abbrev τ : WittVector p k →+* WittVector p k := (WittVector.frobeniusEquiv p k).symm.toRingHom

scoped instance ringHomSurjective_σ : RingHomSurjective (σ p k) := ⟨(WittVector.frobenius_bijective p k).2⟩

scoped instance ringHomSurjective_τ : RingHomSurjective (τ p k) := ⟨(WittVector.frobeniusEquiv p k).symm.surjective⟩

theorem σ_τ (a : WittVector p k) : σ p k (τ p k a) = a :=
  (WittVector.frobeniusEquiv p k).apply_symm_apply a

variable [CharP A p]

theorem map_frobenius_eq (a : WittVector p k) :
    WittVector.map (algebraMap k A) (WittVector.frobenius a) =
      WittVector.frobenius (WittVector.map (algebraMap k A) a) := by
  ext n
  simp only [WittVector.map_coeff, WittVector.coeff_frobenius_charP, map_pow]

theorem φ_σ (N : ℕ) (a : WittVector p k) :
    φ p k A N (σ p k a) = TruncWitt.frobeniusFun (φ p k A N a) := by
  rw [φ_apply, φ_apply, TruncWitt.frobeniusFun_truncate, map_frobenius_eq]

theorem frobeniusFun_mul {N : ℕ} (x y : TruncatedWittVector p N A) :
    TruncWitt.frobeniusFun (x * y) = TruncWitt.frobeniusFun x * TruncWitt.frobeniusFun y := by
  obtain ⟨X, rfl⟩ := WittVector.truncate_surjective p N A x
  obtain ⟨Y, rfl⟩ := WittVector.truncate_surjective p N A y
  rw [← map_mul, TruncWitt.frobeniusFun_truncate, TruncWitt.frobeniusFun_truncate,
    TruncWitt.frobeniusFun_truncate, map_mul, map_mul]

theorem verschiebung_φ_σ_mul {N : ℕ} (b : WittVector p k) (y : TruncatedWittVector p N A) :
    TruncWitt.verschiebung (φ p k A N (σ p k b) * y) = φ p k A N b * TruncWitt.verschiebung y := by
  obtain ⟨Y, rfl⟩ := WittVector.truncate_surjective p N A y
  rw [φ_apply, φ_apply, ← map_mul, TruncWitt.verschiebung_truncate, TruncWitt.verschiebung_truncate,
    ← map_mul, map_frobenius_eq, mul_comm, WittVector.verschiebung_mul_frobenius, mul_comm]

noncomputable def FN (N : ℕ) : wittHomSub p k A N →ₛₗ[σ p k] wittHomSub p k A N where
  toFun y := ⟨TruncWitt.frobeniusFun (y : TruncatedWittVector p N A), frobeniusFun_mem_wittHom y.2⟩
  map_add' x y := Subtype.ext (TruncWitt.frobeniusFun_add (natCast_eq_zero_of_algebra k p A) _ _)
  map_smul' a y := Subtype.ext (by
    change TruncWitt.frobeniusFun (φ p k A N a * (y : TruncatedWittVector p N A)) =
      φ p k A N (σ p k a) * TruncWitt.frobeniusFun (y : TruncatedWittVector p N A)
    rw [frobeniusFun_mul, φ_σ])

@[scoped simp] theorem coe_FN {N : ℕ} (y : wittHomSub p k A N) :
    (FN p k A N y : TruncatedWittVector p N A) = TruncWitt.frobeniusFun (y : TruncatedWittVector p N A) :=
  rfl

noncomputable def VN (N : ℕ) : wittHomSub p k A N →ₛₗ[τ p k] wittHomSub p k A N where
  toFun y := ⟨TruncWitt.verschiebung (y : TruncatedWittVector p N A), verschiebung_mem_wittHom y.2⟩
  map_add' x y := Subtype.ext (map_add _ _ _)
  map_smul' a y := Subtype.ext (by
    change TruncWitt.verschiebung (φ p k A N a * (y : TruncatedWittVector p N A)) =
      φ p k A N (τ p k a) * TruncWitt.verschiebung (y : TruncatedWittVector p N A)
    conv_lhs => rw [← σ_τ p k a]
    rw [verschiebung_φ_σ_mul])

@[scoped simp] theorem coe_VN {N : ℕ} (y : wittHomSub p k A N) :
    (VN p k A N y : TruncatedWittVector p N A) = TruncWitt.verschiebung (y : TruncatedWittVector p N A) :=
  rfl

theorem natCast_smul_eq {N : ℕ} (n : ℕ) (y : wittHomSub p k A N) :
    ((n : WittVector p k) • y : wittHomSub p k A N) = (n : ℤ) • y := by
  apply Subtype.ext
  change φ p k A N n * (y : TruncatedWittVector p N A) = ((n : ℤ) • y : wittHomSub p k A N)
  rw [map_natCast, Submodule.coe_smul_of_tower, natCast_zsmul, nsmul_eq_mul]

theorem FN_VN {N : ℕ} (y : wittHomSub p k A N) : FN p k A N (VN p k A N y) = (p : WittVector p k) • y := by
  rw [natCast_smul_eq]
  apply Subtype.ext
  simp only [coe_FN, coe_VN, Submodule.coe_smul_of_tower]
  exact TruncWitt.frobeniusFun_verschiebung_eq_smul (natCast_eq_zero_of_algebra k p A) _

end HomModule

section Assembly

theorem nontrivial_of_bialgebra (k : Type u) [Field k] (A : Type v) [CommRing A] [Bialgebra k A] :
    Nontrivial A := by
  refine ⟨⟨1, 0, fun h => ?_⟩⟩
  have := congrArg (Coalgebra.counit (R := k) (A := A)) h
  rw [Bialgebra.counit_one, map_zero] at this
  exact one_ne_zero this

theorem charP_of_bialgebra (p : ℕ) (k : Type u) [Field k] [CharP k p] (A : Type v) [CommRing A]
    [Bialgebra k A] : CharP A p :=
  haveI := nontrivial_of_bialgebra k A
  charP_of_injective_algebraMap (algebraMap k A).injective p

variable {p : ℕ} [hp : Fact p.Prime] {k : Type u} [CommRing k] [CharP k p] [PerfectRing k p]
variable {A : Type v} [CommRing A] [Bialgebra k A]

attribute [local instance] wittModule

variable (p k A) in

noncomputable def ofN (N : ℕ) : wittHomSub p k A N →+ DieudonneModule k p A where
  toFun y := DieudonneModule.of k p A N ⟨y, y.2⟩
  map_zero' := map_zero _
  map_add' _ _ := by rw [← map_add]; rfl

theorem ofN_apply {N : ℕ} (y : wittHomSub p k A N) :
    ofN p k A N y = DieudonneModule.of k p A N ⟨y, y.2⟩ := rfl

theorem ofN_injective (N : ℕ) : Injective (ofN p k A N) := fun _ _ h =>
  Subtype.ext (congrArg Subtype.val (DieudonneModule.of_injective N h))

theorem ofN_surjective {N : ℕ} (hN : Surjective (DieudonneModule.of k p A N)) :
    Surjective (ofN p k A N) := fun z => by
  obtain ⟨y, rfl⟩ := hN z
  exact ⟨⟨y, y.2⟩, rfl⟩

theorem ofN_FN [CharP A p] {N : ℕ} (y : wittHomSub p k A N) :
    ofN p k A N (FN p k A N y) = DieudonneModule.frobenius k p A (ofN p k A N y) := by
  rw [ofN_apply, ofN_apply, DieudonneModule.frobenius_of]
  rfl

theorem ofN_VN [CharP A p] {N : ℕ} (y : wittHomSub p k A N) :
    ofN p k A N (VN p k A N y) = DieudonneModule.verschiebung k p A (ofN p k A N y) := by
  rw [ofN_apply, ofN_apply, DieudonneModule.verschiebung_of]
  rfl

theorem ofN_zsmul {N : ℕ} (n : ℤ) (y : wittHomSub p k A N) :
    ofN p k A N (n • y) = n • ofN p k A N y :=
  map_zsmul _ _ _

theorem exists_hondaSystem_of_surjective [IsArtinian k A] [IsNoetherian k A] [CharP A p]
    (L : Submodule ℤ (DieudonneModule k p A)) {N : ℕ}
    (hN : Surjective (DieudonneModule.of k p A N))
    (hL : ∀ (a : WittVector p k) (y : wittHomSub p k A N), ofN p k A N y ∈ L → ofN p k A N (a • y) ∈ L)
    (SH1 : ∀ z : DieudonneModule k p A,
      DieudonneModule.frobenius k p A z ∈ L → ∃ y ∈ L, DieudonneModule.frobenius k p A z = (p : ℤ) • y)
    (SH3 : ∀ z ∈ L, DieudonneModule.verschiebung k p A z = 0 → z = 0)
    (KERF : ∀ z : DieudonneModule k p A, DieudonneModule.frobenius k p A z = 0 →
      ∃ y ∈ L, DieudonneModule.verschiebung k p A y = z)
    (TORS : ∀ z : DieudonneModule k p A, (p : ℤ) • z = 0 →
      ∃ y ∈ L, ∃ x : DieudonneModule k p A, DieudonneModule.verschiebung k p A x = 0 ∧ y + x = z) :
    ∃ H : HondaSystem (p : ℤ) (DieudonneModule k p A),
      H.toDieudonneDatum = DieudonneModule.dieudonneDatum k p A ∧ H.L = L := by
  have hsurj := ofN_surjective (p := p) (k := k) (A := A) hN
  have hinj := ofN_injective (p := p) (k := k) (A := A) N

  let LN : Submodule (WittVector p k) (wittHomSub p k A N) :=
    { carrier := {y | ofN p k A N y ∈ L}
      add_mem' := fun {x y} hx hy => by
        change ofN p k A N (x + y) ∈ L
        rw [map_add]; exact L.add_mem hx hy
      zero_mem' := by change ofN p k A N 0 ∈ L; rw [map_zero]; exact L.zero_mem
      smul_mem' := fun a y hy => hL a y hy }
  have hpsmul : ∀ y : wittHomSub p k A N, ((p : WittVector p k) • y : wittHomSub p k A N) = (p : ℤ) • y :=
    natCast_smul_eq p k A p

  have sh2N : LinearMap.range (FN p k A N) ⊔ LN = ⊤ := by
    refine HondaSystem.range_sup_eq_top_of_isArtinian_of_isNoetherian (FN p k A N) (VN p k A N)
      (p : WittVector p k) (FN_VN p k A) LN ?_ ?_ ?_ ?_
    · rintro y (hy : ofN p k A N y ∈ L) ⟨z, rfl⟩
      rw [ofN_FN] at hy
      obtain ⟨m, hm, hFz⟩ := SH1 _ hy
      obtain ⟨y', rfl⟩ := hsurj m
      refine ⟨y', hm, hinj ?_⟩
      rw [ofN_FN, hFz, hpsmul, ofN_zsmul]
    · rintro y (hy : ofN p k A N y ∈ L) hV
      apply hinj
      rw [map_zero]
      refine SH3 _ hy ?_
      rw [← ofN_VN, hV, map_zero]
    · intro y hy
      rw [LinearMap.mem_ker] at hy
      have hF : DieudonneModule.frobenius k p A (ofN p k A N y) = 0 := by
        rw [← ofN_FN, hy, map_zero]
      obtain ⟨m, -, hm⟩ := KERF _ hF
      obtain ⟨z, rfl⟩ := hsurj m
      refine ⟨z, hinj ?_⟩
      rw [ofN_VN, hm]
    · intro y hy
      have hp0 : (p : ℤ) • ofN p k A N y = 0 := by
        rw [← ofN_zsmul, ← hpsmul, hy, map_zero]
      obtain ⟨m, hm, m', hVm', hsum⟩ := TORS _ hp0
      obtain ⟨a, rfl⟩ := hsurj m
      obtain ⟨b, rfl⟩ := hsurj m'
      refine ⟨a, hm, b, hinj ?_, hinj ?_⟩
      · rw [ofN_VN, hVm', map_zero]
      · rw [map_add, hsum]

  set Dt := DieudonneModule.dieudonneDatum k p A
  refine ⟨{ toDieudonneDatum := Dt, L := L, sh1_le := ?_, sh1_ge := ?_, sh2' := ?_, sh3 := ?_ }, rfl, rfl⟩
  · rintro x hx ⟨z, rfl⟩
    exact SH1 z hx
  · intro y _
    exact ⟨Dt.V y, Dt.F_V_apply y⟩
  · rw [eq_top_iff]
    rintro m -
    obtain ⟨y, rfl⟩ := hsurj m
    have hy : y ∈ LinearMap.range (FN p k A N) ⊔ LN := by rw [sh2N]; exact Submodule.mem_top
    obtain ⟨u, ⟨a, rfl⟩, w, hw, rfl⟩ := Submodule.mem_sup.1 hy
    rw [map_add, ofN_FN]
    exact Submodule.mem_sup.2 ⟨_, ⟨ofN p k A N a, rfl⟩, _, hw, rfl⟩
  · exact SH3

end Assembly

section SpecialFibre

open scoped TensorProduct

attribute [local instance] wittModule

variable {𝓞 : Type u} [CommRing 𝓞] (p : ℕ) [hp : Fact p.Prime]
variable {k : Type v} [CommRing k] [CharP k p] [PerfectRing k p] [Algebra 𝓞 k]
variable (ℛ : Type w) [CommRing ℛ] [HopfAlgebra 𝓞 ℛ]

theorem smul_mem_fontaineKer (hk : Surjective (algebraMap 𝓞 k)) {N : ℕ} (a : WittVector p k)
    {y : TruncatedWittVector p N (k ⊗[𝓞] ℛ)}
    (hy : y ∈ TruncWitt.fontaineKer p N (SpecialFibre.reduction 𝓞 k ℛ)) :
    φ p k (k ⊗[𝓞] ℛ) N a * y ∈ TruncWitt.fontaineKer p N (SpecialFibre.reduction 𝓞 k ℛ) := by
  obtain ⟨X, rfl, hX⟩ := hy
  obtain ⟨B, rfl⟩ := WittVector.map_surjective _ hk a
  refine ⟨WittVector.map (algebraMap 𝓞 ℛ) B * X, ?_, ?_⟩
  · rw [map_mul, map_mul, φ_apply]
    congr 2
    ext n
    simp only [WittVector.map_coeff]
    exact ((Algebra.TensorProduct.includeRight : ℛ →ₐ[𝓞] k ⊗[𝓞] ℛ).commutes (B.coeff n)).trans
      (IsScalarTower.algebraMap_apply 𝓞 k (k ⊗[𝓞] ℛ) _)
  · rw [map_mul]
    exact Ideal.mul_mem_left _ _ hX

theorem exists_hondaSystem_of_level (hpO : (p : 𝓞) ∈ nonZeroDivisors 𝓞)
    (hk : Surjective (algebraMap 𝓞 k))
    (hker : RingHom.ker (algebraMap 𝓞 k) = Ideal.span {(p : 𝓞)})
    [Coalgebra.IsCocomm 𝓞 ℛ] [Module.Free 𝓞 ℛ] [Module.Finite 𝓞 ℛ]
    [IsArtinian k (k ⊗[𝓞] ℛ)] [IsNoetherian k (k ⊗[𝓞] ℛ)] [CharP (k ⊗[𝓞] ℛ) p]
    {N : ℕ} (hN : Surjective (DieudonneModule.of k p (k ⊗[𝓞] ℛ) N)) :
    ∃ H : HondaSystem (p : ℤ) (DieudonneModule k p (k ⊗[𝓞] ℛ)),
      H.toDieudonneDatum = DieudonneModule.dieudonneDatum k p (k ⊗[𝓞] ℛ) ∧
      H.L = fontaineHodge k p (SpecialFibre.reduction 𝓞 k ℛ) := by
  have hpℛ : (p : ℛ) ∈ nonZeroDivisors ℛ := by
    have hreg : IsSMulRegular ℛ (p : 𝓞) := Module.Flat.isSMulRegular_of_nonZeroDivisors hpO
    refine mem_nonZeroDivisors_iff_right.2 fun x hx => hreg ?_
    change (p : 𝓞) • x = (p : 𝓞) • (0 : ℛ)
    rw [smul_zero, Algebra.smul_def, map_natCast, mul_comm, hx]
  have hπker := SpecialFibre.ker_reduction_eq_span (ℛ := ℛ) hk hker
  have hπs := SpecialFibre.reduction_surjective (ℛ := ℛ) hk
  have key := @exists_hondaSystem_of_surjective p _ k _ _ _ (k ⊗[𝓞] ℛ) inferInstance inferInstance
    inferInstance inferInstance inferInstance (fontaineHodge k p (SpecialFibre.reduction 𝓞 k ℛ)) N hN

  have hL : ∀ (a : WittVector p k) (y : wittHomSub p k (k ⊗[𝓞] ℛ) N),
      ofN p k (k ⊗[𝓞] ℛ) N y ∈ fontaineHodge k p (SpecialFibre.reduction 𝓞 k ℛ) →
      ofN p k (k ⊗[𝓞] ℛ) N (a • y) ∈ fontaineHodge k p (SpecialFibre.reduction 𝓞 k ℛ) := by
    intro a y hy
    rw [ofN_apply, of_mem_fontaineHodge_iff hpℛ hπker.le hπs] at hy ⊢
    exact smul_mem_fontaineKer p ℛ hk a hy

  exact key hL
    (fun z hz =>
      Deformation.DieudonneModule.exists_mem_fontaineHodge_frobenius_eq_smul p hpO hk hker ℛ hz)
    (fun z hz hV =>
      @Deformation.DieudonneModule.eq_zero_of_mem_fontaineHodge_of_verschiebung_eq_zero ℛ _ p _ hpℛ k _
        (k ⊗[𝓞] ℛ) inferInstance inferInstance (SpecialFibre.reduction 𝓞 k ℛ) hπker z hz hV)
    (fun z hz =>
      Deformation.DieudonneModule.exists_mem_fontaineHodge_verschiebung_eq_of_frobenius_eq_zero
        p hpO hk hker ℛ hz)
    (fun z hz =>
      Deformation.DieudonneModule.exists_mem_fontaineHodge_add_eq_of_smul_eq_zero p hpO hk hker ℛ hz)

end SpecialFibre

section FieldCase

open scoped TensorProduct

variable {𝓞 : Type u} [CommRing 𝓞] (p : ℕ) [hp : Fact p.Prime]
variable {k : Type v} [Field k] [CharP k p] [PerfectRing k p] [Algebra 𝓞 k]
variable (ℛ : Type w) [CommRing ℛ] [HopfAlgebra 𝓞 ℛ]

theorem exists_hondaSystem (hpO : (p : 𝓞) ∈ nonZeroDivisors 𝓞)
    (hk : Surjective (algebraMap 𝓞 k))
    (hker : RingHom.ker (algebraMap 𝓞 k) = Ideal.span {(p : 𝓞)})
    [Coalgebra.IsCocomm 𝓞 ℛ] [Module.Free 𝓞 ℛ] [Module.Finite 𝓞 ℛ] :
    ∃ H : HondaSystem (p : ℤ) (DieudonneModule k p (k ⊗[𝓞] ℛ)),
      H.toDieudonneDatum = DieudonneModule.dieudonneDatum k p (k ⊗[𝓞] ℛ) ∧
      H.L = fontaineHodge k p (SpecialFibre.reduction 𝓞 k ℛ) := by
  haveI : CharP (k ⊗[𝓞] ℛ) p := charP_of_bialgebra p k (k ⊗[𝓞] ℛ)
  obtain ⟨N, hN⟩ := Deformation.DieudonneModule.exists_surjective_of k p (k ⊗[𝓞] ℛ)
  exact exists_hondaSystem_of_level p ℛ hpO hk hker hN

end FieldCase

end Deformation.FontaineThmOne
p2m_reactivate "P2MW.S_Deformation_DieudonneModule_exists_hondaSystem_L_eq_fontaineHodge.Deformation P2MW.S_Deformation_DieudonneModule_exists_hondaSystem_L_eq_fontaineHodge.Deformation.FontaineThmOne"
p2m_reactivate "P2MW.S_Deformation_DieudonneModule_exists_hondaSystem_L_eq_fontaineHodge.Deformation"

set_option linter.unusedVariables false in

theorem solution
    {𝓞 : Type u} [CommRing 𝓞] (p : ℕ) [Fact p.Prime] (hp : (p : 𝓞) ∈ nonZeroDivisors 𝓞)
    {k : Type v} [Field k] [CharP k p] [PerfectRing k p] [Algebra 𝓞 k]
    (hk : Function.Surjective (algebraMap 𝓞 k))
    (hker : RingHom.ker (algebraMap 𝓞 k) = Ideal.span {(p : 𝓞)})
    (ℛ : Type w) [CommRing ℛ] [HopfAlgebra 𝓞 ℛ] [Coalgebra.IsCocomm 𝓞 ℛ]
    [Module.Free 𝓞 ℛ] [Module.Finite 𝓞 ℛ] (hrank : ∃ a : ℕ, Module.finrank 𝓞 ℛ = p ^ a) :
    ∃ H : Deformation.HondaSystem (p : ℤ) (Deformation.DieudonneModule k p (TensorProduct 𝓞 k ℛ)),
      H.toDieudonneDatum = Deformation.DieudonneModule.dieudonneDatum k p (TensorProduct 𝓞 k ℛ) ∧
      H.L = Deformation.fontaineHodge k p
        (Algebra.TensorProduct.includeRight : ℛ →ₐ[𝓞] TensorProduct 𝓞 k ℛ).toRingHom :=
  Deformation.FontaineThmOne.exists_hondaSystem p ℛ hp hk hker

end S_Deformation_DieudonneModule_exists_hondaSystem_L_eq_fontaineHodge
end P2MW
export P2MW.S_Deformation_DieudonneModule_exists_hondaSystem_L_eq_fontaineHodge (solution)
