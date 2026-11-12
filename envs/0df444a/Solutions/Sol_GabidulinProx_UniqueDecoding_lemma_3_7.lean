-- Prove2me | solution 1 for GabidulinProx.UniqueDecoding.lemma_3_7
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T04:41:33.43723+00:00
-- url     : https://prove2.me/submissions/6262c7e9-f783-42b7-8ee6-55e98022a4a2

import Mathlib
import Definitions.Def_GabidulinProx_UniqueDecoding_Polynomials
import Definitions.Def_GabidulinProx_UniqueDecoding_RankMetric
import Definitions.Def_GabidulinProx_UniqueDecoding_Codes
import Definitions.Def_GabidulinProx_UniqueDecoding_Reconstruction

section
set_option autoImplicit false

namespace GabidulinProx.Dev.L37

open GabidulinProx.UniqueDecoding

section Abstract

variable {K L : Type*} [Field K] [Fintype K] [Field L] [Fintype L] [Algebra K L]

/-- A subspace of at least the given dimension contains one of exactly that dimension. -/
lemma exists_sub {M : Type*} [AddCommGroup M] [Module K M] (C : Submodule K M) (m : ℕ)
    (h : m ≤ Module.finrank K C) :
    ∃ W ≤ C, Module.finrank K W = m := by
  obtain ⟨f, hf⟩ := exists_linearIndependent_of_le_finrank (R := K) (M := C) h
  have hf' : LinearIndependent K (fun i => (f i : M)) :=
    hf.map' C.subtype (Submodule.ker_subtype C)
  refine ⟨Submodule.span K (Set.range fun i => (f i : M)), ?_, ?_⟩
  · rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact (f i).2
  · rw [finrank_span_eq_card hf']
    simp

/-- Every `(e+1)`-dimensional subspace of `V` contains a nonzero kernel element. -/
lemma core (H : L →ₗ[K] Polynomial L) (V : Submodule K L) (n e D : ℕ)
    (S0 : Finset L)
    (hdeg : ∀ x ∈ V, (H x).natDegree ≤ D)
    (hcard : (∑ i ∈ Finset.range (e + 1), Fintype.card K ^ i) * D < S0.card)
    (hV : Module.finrank K V = n)
    (hker : ∀ z ∈ S0, ∃ Kz : Submodule K L, Kz ≤ V ∧ n - e ≤ Module.finrank K Kz ∧
      ∀ x ∈ Kz, (H x).eval z = 0)
    (W : Submodule K L) (hWV : W ≤ V) (hW : Module.finrank K W = e + 1) :
    ∃ x ∈ W, x ≠ 0 ∧ H x = 0 := by
  classical
  haveI : Finite (Projectivization K W) := inferInstance
  letI : Fintype (Projectivization K W) := Fintype.ofFinite _
  have hcardP : Fintype.card (Projectivization K W) =
      ∑ i ∈ Finset.range (e + 1), Fintype.card K ^ i := by
    have := Projectivization.card_of_finrank K W hW
    rw [Nat.card_eq_fintype_card] at this
    simpa [Nat.card_eq_fintype_card] using this
  let P : Polynomial L := ∏ l : Projectivization K W, H (l.rep : L)
  have hP : P = 0 := by
    refine Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero P (ι := S0) (f := Subtype.val) Subtype.val_injective ?_ ?_
    · rintro ⟨z, hz⟩
      obtain ⟨Kz, hKV, hKd, hKz⟩ := hker z hz
      have h1 := Submodule.finrank_sup_add_finrank_inf_eq W Kz
      have h2 : Module.finrank K ↥(W ⊔ Kz) ≤ n := by
        rw [← hV]; exact Submodule.finrank_mono (sup_le hWV hKV)
      have h3 : 0 < Module.finrank K ↥(W ⊓ Kz) := by omega
      obtain ⟨y, hy, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (p := W ⊓ Kz) (by
          intro hb; rw [hb] at h3; simp at h3)
      have hyW : y ∈ W := hy.1
      have hyK : y ∈ Kz := hy.2
      let y' : W := ⟨y, hyW⟩
      have hy'0 : y' ≠ 0 := fun h => hy0 (by simpa [y'] using congrArg Subtype.val h)
      obtain ⟨a, ha⟩ := Projectivization.exists_smul_eq_mk_rep K y' hy'0
      have : (Projectivization.mk K y' hy'0).rep = a • y' := ha.symm
      have hz0 : (H ((Projectivization.mk K y' hy'0).rep : L)).eval z = 0 := by
        rw [this]
        have : ((a • y' : W) : L) = (a : K) • y := rfl
        rw [this, map_smul]
        have hh := hKz y hyK
        rw [Algebra.smul_def, Polynomial.eval_mul]
        simp [Polynomial.algebraMap_apply, hh]
      simp only [P, Polynomial.eval_prod, Polynomial.eval_zero]
      exact Finset.prod_eq_zero (Finset.mem_univ _) hz0
    · calc P.natDegree ≤ ∑ l : Projectivization K W, (H (l.rep : L)).natDegree :=
            Polynomial.natDegree_prod_le _ _
        _ ≤ ∑ _l : Projectivization K W, D :=
            Finset.sum_le_sum fun l _ => hdeg _ (hWV l.rep.2)
        _ = Fintype.card (Projectivization K W) * D := by simp
        _ < Fintype.card S0 := by rw [hcardP, Fintype.card_coe]; exact hcard
  have : ∃ l ∈ (Finset.univ : Finset (Projectivization K W)), H (l.rep : L) = 0 :=
    Finset.prod_eq_zero_iff.mp hP
  obtain ⟨l, -, hl⟩ := this
  exact ⟨l.rep, l.rep.2, fun h => l.rep_nonzero (Subtype.ext h), hl⟩

lemma exists_E (H : L →ₗ[K] Polynomial L) (V : Submodule K L) (n e D : ℕ)
    (S0 : Finset L)
    (hdeg : ∀ x ∈ V, (H x).natDegree ≤ D)
    (hcard : (∑ i ∈ Finset.range (e + 1), Fintype.card K ^ i) * D < S0.card)
    (hV : Module.finrank K V = n)
    (hker : ∀ z ∈ S0, ∃ Kz : Submodule K L, Kz ≤ V ∧ n - e ≤ Module.finrank K Kz ∧
      ∀ x ∈ Kz, (H x).eval z = 0) :
    ∃ E : Submodule K L, E ≤ V ∧ Module.finrank K E = n - e ∧ ∀ x ∈ E, H x = 0 := by
  classical
  -- E' = kernel inside V
  let E' : Submodule K V := (LinearMap.ker H).comap V.subtype
  have hE'ge : n - e ≤ Module.finrank K E' := by
    by_contra hlt
    rw [not_le] at hlt
    obtain ⟨C, hC⟩ := Submodule.exists_isCompl E'
    have hsum := Submodule.finrank_add_eq_of_isCompl hC
    rw [hV] at hsum
    obtain ⟨W', hW'C, hW'⟩ := exists_sub (K := K) (M := V) C (e + 1) (by omega)
    obtain ⟨x, hxW, hx0, hHx⟩ := core H V n e D S0 hdeg hcard hV hker (W'.map V.subtype)
      (by rintro _ ⟨w, -, rfl⟩; exact w.2) (by rw [Submodule.finrank_map_subtype_eq]; exact hW')
    obtain ⟨w, hw, rfl⟩ := hxW
    have hwE : w ∈ E' := by
      show V.subtype w ∈ LinearMap.ker H
      exact hHx
    have : w ∈ C ⊓ E' := ⟨hW'C hw, hwE⟩
    rw [hC.symm.inf_eq_bot] at this
    exact hx0 (by simp at this; simp [this])
  obtain ⟨E1, hE1, hE1d⟩ := exists_sub (K := K) (M := V) E' (n - e) hE'ge
  refine ⟨E1.map V.subtype, ?_, ?_, ?_⟩
  · rintro _ ⟨x, -, rfl⟩; exact x.2
  · rw [Submodule.finrank_map_subtype_eq] ; exact hE1d
  · rintro _ ⟨x, hx, rfl⟩
    exact hE1 hx

end Abstract

section Concrete

variable {K L : Type*} [Field K] [Fintype K] [Field L] [Fintype L] [Algebra K L]

lemma eval_linearized {R : Type*} [CommSemiring R] (q : ℕ) {k : ℕ} (c : Fin k → R) (x : R) :
    (linearized q c).eval x = ∑ i, c i * x ^ (q ^ i.val) := by
  simp [linearized, Polynomial.eval_finsetSum, Polynomial.eval_monomial]

lemma add_pow_card_pow (i : ℕ) (x y : L) :
    (x + y) ^ (Fintype.card K) ^ i = x ^ (Fintype.card K) ^ i + y ^ (Fintype.card K) ^ i := by
  have hp : CharP K (ringChar K) := ringChar.charP K
  have : Fact (ringChar K).Prime := ⟨CharP.char_is_prime K _⟩
  have : CharP L (ringChar K) := charP_of_injective_algebraMap (algebraMap K L).injective _
  obtain ⟨m, -, hm⟩ := FiniteField.card K (ringChar K)
  rw [hm, ← pow_mul]
  exact add_pow_char_pow x y _ _

variable (K) in
/-- `x ↦ x ^ (q ^ i)` as a `K`-linear map. -/
noncomputable def powLin (i : ℕ) : L →ₗ[K] L where
  toFun x := x ^ (Fintype.card K) ^ i
  map_add' x y := add_pow_card_pow i x y
  map_smul' a x := by
    simp only [Algebra.smul_def, mul_pow, RingHom.id_apply]
    rw [← map_pow, FiniteField.pow_card_pow]

variable (K) in
/-- evaluation of a `q`-polynomial as a `K`-linear map. -/
noncomputable def evalLin {k : ℕ} (c : Fin k → L) : L →ₗ[K] L :=
  ∑ i, (LinearMap.mulLeft K (c i)).comp (powLin K i.val)

lemma evalLin_apply {k : ℕ} (c : Fin k → L) (x : L) :
    evalLin K c x = (linearized (Fintype.card K) c).eval x := by
  rw [eval_linearized]
  simp [evalLin, powLin]

lemma exists_lin {k : ℕ} {f : Polynomial L} (hf : IsLinearized (Fintype.card K) k f) :
    ∃ g : L →ₗ[K] L, ∀ x, f.eval x = g x := by
  obtain ⟨c, rfl⟩ := hf
  exact ⟨evalLin K c, fun x => (evalLin_apply c x).symm⟩

/-- `C` as a `K`-linear map. -/
noncomputable def CL : L →ₗ[K] Polynomial L where
  toFun := Polynomial.C
  map_add' := fun _ _ => Polynomial.C_add
  map_smul' a x := by simp [Polynomial.smul_C]

/-- The linear map `x ↦ H_x`. -/
noncomputable def Hmap {k : ℕ} (pt : Fin k → Polynomial L) (A : Polynomial L)
    (g₀ g₁ : L →ₗ[K] L) : L →ₗ[K] Polynomial L :=
  (∑ i, (LinearMap.mulLeft K (pt i)).comp (CL.comp (powLin K i.val))) -
    (LinearMap.mulLeft K A).comp (CL.comp g₀ + (LinearMap.mulLeft K Polynomial.X).comp (CL.comp g₁))

lemma Hmap_apply {k : ℕ} (pt : Fin k → Polynomial L) (A : Polynomial L)
    (g₀ g₁ : L →ₗ[K] L) (x : L) :
    Hmap pt A g₀ g₁ x = familyEval (Fintype.card K) pt x -
      A * (Polynomial.C (g₀ x) + Polynomial.X * Polynomial.C (g₁ x)) := by
  simp [Hmap, familyEval, CL, powLin]


lemma natDegree_Hmap_le {k : ℕ} (pt : Fin k → Polynomial L) (s m : ℕ)
    (hpt : ∀ j, (pt j).natDegree ≤ s * m + 1) (a₀ : Polynomial L)
    (g₀ g₁ : L →ₗ[K] L) (x : L) (hm : a₀.natDegree ≤ s) :
    (Hmap pt (a₀ ^ m) g₀ g₁ x).natDegree ≤ s * m + 1 := by
  rw [Hmap_apply]
  refine (Polynomial.natDegree_sub_le _ _).trans (max_le ?_ ?_)
  · unfold familyEval
    apply Polynomial.natDegree_sum_le_of_forall_le
    intro i _
    refine (Polynomial.natDegree_mul_le).trans ?_
    simpa using hpt i
  · refine (Polynomial.natDegree_mul_le).trans ?_
    have h1 : (a₀ ^ m).natDegree ≤ s * m := by
      calc (a₀ ^ m).natDegree ≤ m * a₀.natDegree := Polynomial.natDegree_pow_le
        _ ≤ m * s := Nat.mul_le_mul_left _ hm
        _ = s * m := mul_comm _ _
    have h2 : (Polynomial.C (g₀ x) + Polynomial.X * Polynomial.C (g₁ x)).natDegree ≤ 1 := by
      compute_degree
    omega

lemma eval_Hmap {k : ℕ} (pt : Fin k → Polynomial L) (A : Polynomial L)
    (g₀ g₁ : L →ₗ[K] L) (x z : L) :
    (Hmap pt A g₀ g₁ x).eval z =
      (specialize (Fintype.card K) pt z).eval x - A.eval z * (g₀ x + z * g₁ x) := by
  rw [Hmap_apply, Polynomial.eval_sub, specialize, eval_linearized]
  simp only [familyEval, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_add, Polynomial.eval_X]

end Concrete

end GabidulinProx.Dev.L37

namespace GabidulinProx.UniqueDecoding

open GabidulinProx.Dev.L37

theorem chk_lemma_3_7 {K L : Type*} [Field K] [Fintype K] [Field L] [Fintype L]
    [Algebra K L] {n k e : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n) (he : 1 ≤ e)
    (hdec : 2 * e < n - k + 1) (α : Fin n → L) (hα : LinearIndependent K α)
    (u₀ u₁ : Fin n → L) (f₀ f₁ : Polynomial L)
    (hf₀ : IsLinearized (Fintype.card K) n f₀)
    (hf₁ : IsLinearized (Fintype.card K) n f₁)
    (hu₀ : ∀ r, f₀.eval (α r) = u₀ r) (hu₁ : ∀ r, f₁.eval (α r) = u₁ r)
    (a₀ : Polynomial L)
    (hdeg : a₀.natDegree ≤ sigma (Fintype.card K) e - 1)
    (Pz : L → Polynomial L)
    (hPz : DecodedFamily K α u₀ u₁ k e (goodParameters K α k e u₀ u₁) Pz)
    (pt : Fin k → Polynomial L)
    (hpt : ∀ j, (pt j).natDegree ≤ clearingBound (Fintype.card K) k e)
    (hspec : ∀ z ∈ regularParameters (goodParameters K α k e u₀ u₁) a₀,
      specialize (Fintype.card K) pt z =
        Polynomial.C (a₀.eval z ^ (sigma (Fintype.card K) (k - 1))) * Pz z)
    (hlarge : sigma (Fintype.card K) e * clearingBound (Fintype.card K) k e <
      (regularParameters (goodParameters K α k e u₀ u₁) a₀).card) :
    ∃ E : Submodule K L, E ≤ Submodule.span K (Set.range α) ∧ Module.finrank K E = n - e ∧
      ∀ x ∈ E, familyEval (Fintype.card K) pt x =
        a₀ ^ (sigma (Fintype.card K) (k - 1)) *
          (Polynomial.C (f₀.eval x) + Polynomial.X * Polynomial.C (f₁.eval x)) := by
  classical
  obtain ⟨g₀, hg₀⟩ := exists_lin (K := K) hf₀
  obtain ⟨g₁, hg₁⟩ := exists_lin (K := K) hf₁
  set q := Fintype.card K with hq
  set m := sigma q (k - 1) with hm
  set H := Hmap pt (a₀ ^ m) g₀ g₁ with hH
  set V := Submodule.span K (Set.range α) with hV
  have hVn : Module.finrank K V = n := by
    rw [hV, finrank_span_eq_card hα]; simp
  have hHx : ∀ x, H x = familyEval q pt x -
      a₀ ^ m * (Polynomial.C (f₀.eval x) + Polynomial.X * Polynomial.C (f₁.eval x)) := by
    intro x; rw [hH, Hmap_apply, hg₀, hg₁]
  have hker : ∀ z ∈ regularParameters (goodParameters K α k e u₀ u₁) a₀,
      ∃ Kz : Submodule K L, Kz ≤ V ∧ n - e ≤ Module.finrank K Kz ∧
        ∀ x ∈ Kz, (H x).eval z = 0 := by
    intro z hz
    have hz' : z ∈ goodParameters K α k e u₀ u₁ ∧ a₀.eval z ≠ 0 := by
      simpa [regularParameters] using hz
    obtain ⟨hzg, hza⟩ := hz'
    obtain ⟨hlin, hrank⟩ := hPz z hzg
    obtain ⟨gP, hgP⟩ := exists_lin (K := K) hlin
    let ψ : L →ₗ[K] L := g₀ + (LinearMap.mulLeft K z).comp g₁ - gP
    have hψα : ∀ r, ψ (α r) = (linePoint u₀ u₁ z - evaluateWord α (Pz z)) r := by
      intro r
      simp [ψ, linePoint, evaluateWord, ← hgP, ← hg₀, ← hg₁, hu₀, hu₁]
    have hmap : Submodule.map ψ V = Submodule.span K (Set.range (linePoint u₀ u₁ z - evaluateWord α (Pz z))) := by
      rw [hV, Submodule.map_span, ← Set.range_comp]
      congr 2
      funext r
      exact hψα r
    have hrk : Module.finrank K (Submodule.map ψ V) ≤ e := by
      rw [hmap]; exact hrank
    have hrn := LinearMap.finrank_range_add_finrank_ker (ψ.domRestrict V)
    rw [LinearMap.range_domRestrict, hVn] at hrn
    refine ⟨(LinearMap.ker (ψ.domRestrict V)).map V.subtype, ?_, ?_, ?_⟩
    · rintro _ ⟨w, -, rfl⟩; exact w.2
    · rw [Submodule.finrank_map_subtype_eq]; omega
    · rintro _ ⟨w, hw, rfl⟩
      have hw' : ψ (w : L) = 0 := hw
      have hw'' : g₀ w + z * g₁ w = gP w := by
        simp only [ψ, LinearMap.sub_apply, LinearMap.add_apply, LinearMap.comp_apply, LinearMap.mulLeft_apply] at hw'
        linear_combination hw'
      rw [hH, eval_Hmap, hspec z hz, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
        hgP]
      have h3 : (V.subtype w) = (w : L) := rfl
      rw [h3, hw'']
      ring
  obtain ⟨E, hEV, hEd, hE⟩ := exists_E H V n e (clearingBound q k e)
    (regularParameters (goodParameters K α k e u₀ u₁) a₀)
    (fun x _ => natDegree_Hmap_le pt (sigma q e - 1) m hpt a₀ g₀ g₁ x hdeg)
    hlarge hVn hker
  refine ⟨E, hEV, hEd, fun x hx => ?_⟩
  have := hE x hx
  rw [hHx] at this
  exact sub_eq_zero.mp this

end GabidulinProx.UniqueDecoding

end

theorem solution : type_of% @GabidulinProx.UniqueDecoding.chk_lemma_3_7 := @GabidulinProx.UniqueDecoding.chk_lemma_3_7
