-- Prove2me | solution 1 for BookProof.NavierStokesFlow.CanonicalVector.canH_eq_velH
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung
-- created : 2026-10-22T05:46:46.410955+00:00
-- url     : https://prove2.me/submissions/34eb094a-04dc-4616-ab23-7d8d24700a9f

import Mathlib
import Definitions.Def_ChapterNavierStokesCanonicalVector
import Definitions.Def_ChapterNavierStokesEsa
import Definitions.Def_ChapterNavierStokesIkebeKato
import Definitions.Def_ChapterNavierStokesThreeComponent
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.CanonicalVector


open scoped ENNReal



open LpNat BookProof.FarisLavine IkebeKato ThreeComponent ShiftHamiltonian SignedShift

variable (A : Matrix (Fin 3) (Fin 3) ℝ) (c : Fin 3 → ℝ)

namespace CVP

theorem lower_raise_comm {i k : Fin 3} (h : i ≠ k) (γ : Vel) :
    lower k (raise i γ) = raise i (lower k γ) := by
  funext j
  simp only [raise, lower, Function.update_apply]
  split_ifs <;> subst_vars <;> simp_all

theorem lower_lower_comm (i k : Fin 3) (γ : Vel) :
    lower k (lower i γ) = lower i (lower k γ) := by
  funext j
  simp only [lower, Function.update_apply]
  split_ifs <;> subst_vars <;> simp_all

theorem raise_raise_comm (i k : Fin 3) (γ : Vel) :
    raise k (raise i γ) = raise i (raise k γ) := by
  funext j
  simp only [raise, Function.update_apply]
  split_ifs <;> subst_vars <;> simp_all

theorem cc_comm {i k : Fin 3} (h : i ≠ k) (X : Vel → ℂ) :
    cFun i (cFun k X) = cFun k (cFun i X) := by
  funext γ
  simp only [cFun]
  rw [lower_of_ne (Ne.symm h), lower_of_ne h, lower_lower_comm]
  ring

theorem aa_comm {i k : Fin 3} (h : i ≠ k) (X : Vel → ℂ) :
    aFun i (aFun k X) = aFun k (aFun i X) := by
  funext γ
  simp only [aFun]
  rw [raise_of_ne (Ne.symm h), raise_of_ne h, raise_raise_comm]
  ring

theorem ac_comm {i k : Fin 3} (h : i ≠ k) (X : Vel → ℂ) :
    aFun i (cFun k X) = cFun k (aFun i X) := by
  funext γ
  simp only [aFun, cFun]
  rw [raise_of_ne (Ne.symm h), lower_of_ne h, lower_raise_comm h]
  ring

theorem cFun_add (i : Fin 3) (X Y : Vel → ℂ) : cFun i (X + Y) = cFun i X + cFun i Y := by
  funext γ; simp only [cFun, Pi.add_apply]; ring
theorem aFun_add (i : Fin 3) (X Y : Vel → ℂ) : aFun i (X + Y) = aFun i X + aFun i Y := by
  funext γ; simp only [aFun, Pi.add_apply]; ring
theorem cFun_sub (i : Fin 3) (X Y : Vel → ℂ) : cFun i (X - Y) = cFun i X - cFun i Y := by
  funext γ; simp only [cFun, Pi.sub_apply]; ring
theorem aFun_sub (i : Fin 3) (X Y : Vel → ℂ) : aFun i (X - Y) = aFun i X - aFun i Y := by
  funext γ; simp only [aFun, Pi.sub_apply]; ring
theorem cFun_smul (i : Fin 3) (r : ℂ) (X : Vel → ℂ) : cFun i (r • X) = r • cFun i X := by
  funext γ; simp only [cFun, Pi.smul_apply, smul_eq_mul]; ring
theorem aFun_smul (i : Fin 3) (r : ℂ) (X : Vel → ℂ) : aFun i (r • X) = r • aFun i X := by
  funext γ; simp only [aFun, Pi.smul_apply, smul_eq_mul]; ring
theorem cFun_sum (i : Fin 3) (f : Fin 3 → Vel → ℂ) : cFun i (∑ k, f k) = ∑ k, cFun i (f k) := by
  funext γ; simp only [cFun, Finset.sum_apply, Finset.mul_sum]
theorem aFun_sum (i : Fin 3) (f : Fin 3 → Vel → ℂ) : aFun i (∑ k, f k) = ∑ k, aFun i (f k) := by
  funext γ; simp only [aFun, Finset.sum_apply, Finset.mul_sum]

theorem pFun_lin_add (k : Fin 3) (X Y : Vel → ℂ) : pFun k (X + Y) = pFun k X + pFun k Y := by
  simp only [pFun, cFun_add, aFun_add, smul_add]; abel
theorem mFun_lin_add (k : Fin 3) (X Y : Vel → ℂ) : mFun k (X + Y) = mFun k X + mFun k Y := by
  simp only [mFun, cFun_add, aFun_add, smul_sub, smul_add]; abel
theorem pFun_lin_smul (k : Fin 3) (r : ℂ) (X : Vel → ℂ) : pFun k (r • X) = r • pFun k X := by
  simp only [pFun, cFun_smul, aFun_smul, smul_add, smul_comm r]
theorem mFun_lin_smul (k : Fin 3) (r : ℂ) (X : Vel → ℂ) : mFun k (r • X) = r • mFun k X := by
  simp only [mFun, cFun_smul, aFun_smul, smul_sub, smul_comm r]
theorem mFun_lin_sum (i : Fin 3) (f : Fin 3 → Vel → ℂ) : mFun i (∑ k, f k) = ∑ k, mFun i (f k) := by
  simp only [mFun, cFun_sum, aFun_sum, ← Finset.sum_sub_distrib, Finset.smul_sum]
theorem pFun_lin_sum (i : Fin 3) (f : Fin 3 → Vel → ℂ) : pFun i (∑ k, f k) = ∑ k, pFun i (f k) := by
  simp only [pFun, cFun_sum, aFun_sum, ← Finset.sum_add_distrib, Finset.smul_sum]

/-- the eight-term expansion -/
theorem symProd_expand (i k : Fin 3) (X : Vel → ℂ) (γ : Vel) :
    symProdFun i k X γ = (Complex.I / 4) * ((1 / Real.sqrt 2 : ℝ) : ℂ) ^ 2 * 2 *
      (cFun i (cFun k X) γ + cFun i (aFun k X) γ - aFun i (cFun k X) γ - aFun i (aFun k X) γ
       + cFun k (cFun i X) γ - cFun k (aFun i X) γ + aFun k (cFun i X) γ - aFun k (aFun i X) γ) := by
  simp only [symProdFun, mFun, pFun, cFun_add, aFun_add, cFun_sub, aFun_sub, cFun_smul, aFun_smul,
    Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

end CVP

namespace CVP

theorem half_sq : (((1 / Real.sqrt 2 : ℝ) : ℂ)) ^ 2 = 1 / 2 := by
  rw [← Complex.ofReal_pow, div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  push_cast; ring

theorem symProd_expand' (i k : Fin 3) (X : Vel → ℂ) (γ : Vel) :
    symProdFun i k X γ = (Complex.I / 4) *
      (cFun i (cFun k X) γ + cFun i (aFun k X) γ - aFun i (cFun k X) γ - aFun i (aFun k X) γ
       + cFun k (cFun i X) γ - cFun k (aFun i X) γ + aFun k (cFun i X) γ - aFun k (aFun i X) γ) := by
  rw [symProd_expand, half_sq]; ring

theorem canFun_expand (X : Vel → ℂ) (γ : Vel) :
    canFun A c X γ = ∑ i, ((∑ k, ((A i k : ℝ) : ℂ) * symProdFun i k X γ)
      + ((c i : ℝ) : ℂ) * mFun i X γ) := by
  unfold canFun
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [vFun, mFun_lin_add, mFun_lin_sum, mFun_lin_smul, Pi.add_apply, Finset.sum_apply,
    Pi.smul_apply, smul_eq_mul]
  have : (∑ k, ((A i k : ℝ) : ℂ) * symProdFun i k X γ)
      = (1 / 2 : ℂ) * ((∑ k, ((A i k : ℝ) : ℂ) * mFun i (pFun k X) γ)
        + ∑ k, ((A i k : ℝ) : ℂ) * pFun k (mFun i X) γ) := by
    rw [← Finset.sum_add_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [symProdFun]; ring
  rw [this]; ring

noncomputable def QQ (X : Vel → ℂ) (γ : Vel) (i k : Fin 3) : ℂ :=
  Complex.I * ((if i = k then ((A i i / 2 : ℝ) : ℂ) * (cFun i (cFun i X) γ - aFun i (aFun i X) γ) else 0)
    + ((coefPair A i k : ℝ) : ℂ) * (cFun i (cFun k X) γ - aFun i (aFun k X) γ)
    + ((coefRot A i k : ℝ) : ℂ) * (cFun i (aFun k X) γ - aFun i (cFun k X) γ))

theorem pair_sym (X : Vel → ℂ) (γ : Vel) (i k : Fin 3) :
    ((A i k : ℝ) : ℂ) * symProdFun i k X γ + ((A k i : ℝ) : ℂ) * symProdFun k i X γ
      = QQ A X γ i k + QQ A X γ k i := by
  rw [symProd_expand', symProd_expand']
  by_cases h : i = k
  · subst h
    simp only [QQ, if_true, coefPair, coefRot]
    push_cast; ring
  · rw [← cc_comm h, ← aa_comm h, ← ac_comm h, ac_comm (Ne.symm h)]
    simp only [QQ, if_neg h, if_neg (Ne.symm h), coefPair, coefRot]
    rw [← cc_comm h, ← aa_comm h, ← ac_comm h, ac_comm (Ne.symm h)]
    push_cast; ring

theorem sum_sym {f : Fin 3 → Fin 3 → ℂ} {g : Fin 3 → Fin 3 → ℂ}
    (h : ∀ i k, f i k + f k i = g i k + g k i) : ∑ i, ∑ k, f i k = ∑ i, ∑ k, g i k := by
  have h1 : ∑ i, ∑ k, (f i k + f k i) = ∑ i, ∑ k, (g i k + g k i) := by
    simp only [h]
  simp only [Finset.sum_add_distrib] at h1
  rw [Finset.sum_comm (f := fun i k => f k i), Finset.sum_comm (f := fun i k => g k i)] at h1
  linear_combination h1 / 2

theorem canFun_eq_ladFun (X : Vel → ℂ) (γ : Vel) : canFun A c X γ = ladFun A c X γ := by
  rw [canFun_expand, Finset.sum_add_distrib, sum_sym (pair_sym A X γ)]
  simp only [ladFun, QQ, Finset.mul_sum, mul_add, Finset.sum_add_distrib]
  have hd : ∑ i, ∑ k, Complex.I * (if i = k then ((A i i / 2 : ℝ) : ℂ) *
      (cFun i (cFun i X) γ - aFun i (aFun i X) γ) else 0)
      = ∑ i, Complex.I * (((A i i / 2 : ℝ) : ℂ) * (cFun i (cFun i X) γ - aFun i (aFun i X) γ)) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [mul_ite]
  rw [hd]
  have hc : ∑ i, ((c i : ℝ) : ℂ) * mFun i X γ
      = ∑ i, Complex.I * (((c i / Real.sqrt 2 : ℝ) : ℂ) * (cFun i X γ - aFun i X γ)) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [mFun, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    push_cast; ring
  rw [hc]
  ring

end CVP

namespace CVP

theorem lower_raise_self (i : Fin 3) (β : Vel) : lower i (raise i β) = β := by
  funext j
  by_cases hj : j = i
  · subst hj; simp
  · rw [lower_of_ne hj, raise_of_ne hj]

theorem hFun_eq {sym : Vel → ℝ} (S : SignedHop Vel sym) (X T : Vel → ℂ)
    (h1 : ∀ α, T (S.shift α) = (S.amp α : ℂ) * X α)
    (h0 : ∀ γ, (¬ ∃ α, S.shift α = γ) → T γ = 0) (γ : Vel) :
    S.hFun X γ = Complex.I * (T γ - (S.amp γ : ℂ) * X (S.shift γ)) := by
  unfold SignedHop.hFun
  congr 2
  by_cases hb : ∃ α, S.maj.shift α = γ
  · obtain ⟨α, rfl⟩ := hb
    rw [ShiftData.hop_shift]
    exact (h1 α).symm
  · rw [ShiftData.hop_eq_zero _ _ hb]
    exact (h0 γ hb).symm

theorem csqrt_mul (x y : ℝ) (hx : 0 ≤ x) :
    ((Real.sqrt (x * y) : ℝ) : ℂ) = (Real.sqrt x : ℂ) * (Real.sqrt y : ℂ) := by
  rw [Real.sqrt_mul hx]; push_cast; ring

theorem diag_coord (i : Fin 3) (X : Vel → ℂ) (γ : Vel) :
    (diagHop A c i).hFun X γ
      = Complex.I * (((A i i / 2 : ℝ) : ℂ) * (cFun i (cFun i X) γ - aFun i (aFun i X) γ)) := by
  rw [hFun_eq (diagHop A c i) X (fun γ => ((A i i / 2 : ℝ) : ℂ) * cFun i (cFun i X) γ)]
  · congr 1
    simp only [diagHop, ampDiag, shDiag, aFun, raise_self]
    rw [Real.sqrt_mul (by positivity)]
    push_cast
    ring_nf
  · intro α
    simp only [diagHop, ampDiag, shDiag, cFun, raise_self, lower_raise_self]
    rw [Real.sqrt_mul (by positivity)]
    push_cast
    ring_nf
  · intro γ hγ
    simp only [diagHop, shDiag] at hγ
    simp only [cFun, lower_self]
    by_cases h2 : 2 ≤ γ i
    · exfalso
      apply hγ
      refine ⟨lower i (lower i γ), ?_⟩
      rw [raise_lower i (by simp; omega), raise_lower i (by omega)]
    · have : γ i = 0 ∨ γ i - 1 = 0 := by omega
      rcases this with h | h <;> simp [h]

theorem shear_coord (i : Fin 3) (X : Vel → ℂ) (γ : Vel) :
    (shearHop A c i).hFun X γ
      = Complex.I * (((c i / Real.sqrt 2 : ℝ) : ℂ) * (cFun i X γ - aFun i X γ)) := by
  rw [hFun_eq (shearHop A c i) X (fun γ => ((c i / Real.sqrt 2 : ℝ) : ℂ) * cFun i X γ)]
  · congr 1
    simp only [shearHop, ampShear, shShear, aFun]
    push_cast; ring
  · intro α
    simp only [shearHop, ampShear, shShear, cFun, raise_self, lower_raise_self]
    push_cast; ring
  · intro γ hγ
    simp only [shearHop, shShear] at hγ
    simp only [cFun]
    by_cases h1 : 1 ≤ γ i
    · exact absurd ⟨lower i γ, raise_lower i h1⟩ hγ
    · have : γ i = 0 := by omega
      simp [this]

end CVP

namespace CVP

theorem pair_coord (i k : Fin 3) (X : Vel → ℂ) (γ : Vel) :
    (pairHop A c i k).hFun X γ
      = Complex.I * (((coefPair A i k : ℝ) : ℂ) * (cFun i (cFun k X) γ - aFun i (aFun k X) γ)) := by
  by_cases hik : i = k
  · subst hik
    have h0 : coefPair A i i = 0 := by simp [coefPair]
    rw [hFun_eq (pairHop A c i i) X (fun _ => 0)]
    · simp [pairHop, ampPair, h0]
    · intro α; simp [pairHop, ampPair, h0]
    · intro _ _; rfl
  rw [hFun_eq (pairHop A c i k) X (fun γ => ((coefPair A i k : ℝ) : ℂ) * cFun i (cFun k X) γ)]
  · congr 1
    simp only [pairHop, ampPair, shPair, aFun, raise_of_ne (Ne.symm hik), raise_raise_comm i k]
    rw [Real.sqrt_mul (by positivity)]
    push_cast; ring
  · intro α
    simp only [pairHop, ampPair, shPair, cFun, raise_self, lower_raise_self,
      raise_of_ne hik]
    rw [Real.sqrt_mul (by positivity)]
    push_cast; ring
  · intro γ hγ
    simp only [pairHop, shPair] at hγ
    simp only [cFun, lower_of_ne (Ne.symm hik)]
    by_cases h1 : 1 ≤ γ i
    · by_cases h2 : 1 ≤ γ k
      · exfalso; apply hγ
        refine ⟨lower k (lower i γ), ?_⟩
        rw [raise_lower k (by rw [lower_of_ne (Ne.symm hik)]; exact h2), raise_lower i h1]
      · have : γ k = 0 := by omega
        simp [this]
    · have : γ i = 0 := by omega
      simp [this]

theorem rot_coord (i k : Fin 3) (X : Vel → ℂ) (γ : Vel) :
    (rotHop A c i k).hFun X γ
      = Complex.I * (((coefRot A i k : ℝ) : ℂ) * (cFun i (aFun k X) γ - aFun i (cFun k X) γ)) := by
  by_cases hik : i = k
  · subst hik
    have h0 : coefRot A i i = 0 := by simp [coefRot]
    rw [hFun_eq (rotHop A c i i) X (fun _ => 0)]
    · simp [rotHop, ampRot, h0]
    · intro α; simp [rotHop, ampRot, h0]
    · intro _ _; rfl
  rw [hFun_eq (rotHop A c i k) X (fun γ => ((coefRot A i k : ℝ) : ℂ) * cFun i (aFun k X) γ)]
  · congr 1
    simp only [rotHop, ampRot, shRot, aFun, cFun, raise_of_ne (Ne.symm hik)]
    by_cases hk : γ k = 0
    · simp [hk]
    · rw [if_neg hk, lower_raise_comm hik, Real.sqrt_mul (by positivity)]
      push_cast; ring
  · intro α
    simp only [rotHop, ampRot, shRot]
    by_cases hk : α k = 0
    · rw [if_pos hk]
      simp only [cFun, swapVel_apply, Equiv.swap_apply_left, hk]
      simp
    · rw [if_neg hk]
      have hk1 : 1 ≤ α k := by omega
      simp only [cFun, aFun, raise_self, lower_raise_self, lower_of_ne hik, raise_lower k hk1,
        lower_self]
      rw [Real.sqrt_mul (by positivity)]
      have : ((α k - 1 : ℕ) : ℝ) + 1 = (α k : ℝ) := by
        rw [Nat.cast_sub hk1]; push_cast; ring
      rw [this]
      push_cast; ring
  · intro γ hγ
    simp only [rotHop] at hγ
    simp only [cFun]
    by_cases h1 : 1 ≤ γ i
    · exfalso; apply hγ
      refine ⟨raise k (lower i γ), ?_⟩
      have hne : raise k (lower i γ) k ≠ 0 := by simp
      simp only [shRot, if_neg hne, lower_raise_self, raise_lower i h1]
    · have : γ i = 0 := by omega
      simp [this]

end CVP

namespace CVP

noncomputable def crdL : lpFiniteModes Vel →ₗ[ℂ] (Vel → ℂ) where
  toFun x := ((x : L2I Vel) : Vel → ℂ)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem crdL_apply (x : lpFiniteModes Vel) : crdL x = ((x : L2I Vel) : Vel → ℂ) := rfl

theorem crdL_mom (i : Fin 3) (y : lpFiniteModes Vel) : crdL (mom i y) = mFun i (crdL y) := by
  simp only [mom, LinearMap.smul_apply, LinearMap.sub_apply, map_smul, map_sub]
  rfl

theorem crdL_pos (i : Fin 3) (y : lpFiniteModes Vel) : crdL (pos i y) = pFun i (crdL y) := by
  simp only [pos, LinearMap.smul_apply, LinearMap.add_apply, map_smul, map_add]
  rfl

theorem crdL_fieldV (i : Fin 3) (y : lpFiniteModes Vel) :
    crdL (fieldV A c i y) = vFun A c i (crdL y) := by
  simp only [fieldV, vFun, LinearMap.add_apply, LinearMap.sum_apply, Finset.sum_apply,
    LinearMap.smul_apply, LinearMap.id_apply, map_add, map_sum, map_smul, crdL_pos]

theorem crdL_canH (x : lpFiniteModes Vel) (γ : Vel) :
    crdL (canH A c x) γ = canFun A c (crdL x) γ := by
  simp only [canH, LinearMap.sum_apply, Finset.sum_apply, LinearMap.smul_apply,
    LinearMap.add_apply, LinearMap.comp_apply, map_sum, map_smul, map_add, crdL_mom,
    crdL_fieldV, canFun, Pi.smul_apply, Pi.add_apply, smul_eq_mul]

theorem listH_coord {sym : Vel → ℝ} (L : List (SignedHop Vel sym)) (x : maxDom sym) (γ : Vel) :
    ((SignedShift.listH L x : L2I Vel) : Vel → ℂ) γ
      = (L.map fun S => S.hFun ((x : L2I Vel) : Vel → ℂ) γ).sum := by
  induction L with
  | nil => simp [SignedShift.listH]
  | cons S L ih =>
    simp only [SignedShift.listH, List.map_cons, List.sum_cons, LinearMap.add_apply,
      lp.coeFn_add, Pi.add_apply] at ih ⊢
    rw [ih]
    rfl

end CVP

theorem solution :
    (lpFiniteModes Vel).subtype.comp (canH A c)
      = (velH A c).comp (Submodule.inclusion (finiteModes_le_maxDom (velSym (velMu A c)))) := by
  refine LinearMap.ext fun x => lp.ext (funext fun γ => ?_)
  change CVP.crdL (canH A c x) γ = _
  rw [CVP.crdL_canH, CVP.canFun_eq_ladFun, LinearMap.comp_apply, velH, CVP.listH_coord]
  change _ = ((hopList A c).map fun S => S.hFun (CVP.crdL x) γ).sum
  simp only [hopList, List.finRange_succ, List.finRange_zero, List.flatMap_cons, List.flatMap_nil,
    List.map_cons, List.map_nil, List.map_append, List.sum_cons, List.sum_nil, List.sum_append,
    List.append_nil, List.cons_append, List.nil_append, List.map_map, Function.comp_apply]
  simp only [CVP.diag_coord, CVP.shear_coord, CVP.pair_coord, CVP.rot_coord, ladFun,
    Fin.sum_univ_three]
  simp only [Fin.succ_zero_eq_one, Fin.succ_one_eq_two]
  ring
