-- Prove2me | solution 1 for BoxTDIMinMax.Separable.theorem_3_3
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T00:09:17.105122+00:00
-- url     : https://prove2.me/submissions/41b32a0b-c9e0-4dec-bbc4-905ec604b924
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_BoxTDIMinMax_Separable_Setting
import Theorems.Thm_BoxTDIMinMax_Separable_lemma_3_2
import Theorems.Thm_BoxTDIMinMax_Separable_claim_3_4
import Theorems.Thm_BoxTDIMinMax_Separable_theorem_2_12
import Theorems.Thm_BoxTDIMinMax_Separable_proposition_2_1
import Theorems.Thm_BoxTDIMinMax_Separable_cook_fonlupt_schrijver

open Matrix BoxTDIMinMax.Separable

namespace BoxTDIMinMax.Separable.Thm33Aux

theorem untop (x : WithTop ℤ) (hx : x ≠ ⊤) : ((x.untopD 0 : ℤ) : WithTop ℤ) = x := by
  obtain ⟨a, rfl⟩ := WithTop.ne_top_iff_exists.mp hx
  rfl

theorem ratMat_map {ι S : Type*} (Q : Matrix ι S ℤ) :
    (ratMat Q).map ((↑) : ℚ → ℝ) = Q.map ((↑) : ℤ → ℝ) := by
  ext i s; simp [ratMat]

/-- Real dual feasibility of an integral vector is integral feasibility. -/
theorem dualFeas_int {ι S : Type*} [Fintype ι] [Fintype S] (Q : Matrix ι S ℤ) (c : S → ℤ)
    (y : ι → ℤ) : (fun i => (y i : ℝ)) ∈ DualFeas (ratMat Q) c ↔ 0 ≤ y ∧ y ᵥ* Q = c := by
  unfold DualFeas
  simp only [Set.mem_setOf_eq, ratMat_map]
  constructor
  · rintro ⟨h0, h1⟩
    refine ⟨fun i => by have := h0 i; simp only [Pi.zero_apply] at this ⊢; exact_mod_cast this, ?_⟩
    funext s
    have := congrFun h1 s
    simp only [vecMul, dotProduct, Matrix.map_apply] at this
    simp only [vecMul, dotProduct]
    exact_mod_cast this
  · rintro ⟨h0, h1⟩
    refine ⟨fun i => by have := h0 i; simp only [Pi.zero_apply] at this ⊢; exact_mod_cast this, ?_⟩
    funext s
    have := congrFun h1 s
    simp only [vecMul, dotProduct, Matrix.map_apply]
    simp only [vecMul, dotProduct] at this
    exact_mod_cast this

/-- Weak LP duality bound: for dual feasible `y'` and `z ∈ R̈`, `y' p ≤ c z`. -/
theorem dualObj_le {ι S : Type*} [Fintype ι] [Fintype S] (Q : Matrix ι S ℤ) (p : ι → ℤ)
    (c : S → ℤ) (z : S → ℤ) (hz : z ∈ intPts Q p) (y' : ι → ℝ)
    (hy' : y' ∈ DualFeas (ratMat Q) c) :
    dualObj (ratVec p) y' ≤ ∑ s, (c s : ℝ) * (z s : ℝ) := by
  obtain ⟨h0, h1⟩ := hy'
  rw [ratMat_map] at h1
  unfold dualObj ratVec
  have hc : ∀ s, (c s : ℝ) = ∑ i, y' i * (Q i s : ℝ) := by
    intro s
    have := congrFun h1 s
    simp only [vecMul, dotProduct, Matrix.map_apply] at this
    exact this.symm
  calc ∑ i, y' i * (((p i : ℚ)) : ℝ)
      ≤ ∑ i, y' i * ∑ s, (Q i s : ℝ) * (z s : ℝ) := by
        refine Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left ?_ (h0 i))
        have := hz i
        simp only [mulVec, dotProduct] at this
        push_cast
        exact_mod_cast this
    _ = ∑ s, (c s : ℝ) * (z s : ℝ) := by
        simp_rw [hc, Finset.mul_sum, Finset.sum_mul]
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl (fun _ _ => Finset.sum_congr rfl (fun _ _ => by ring))

theorem dualObj_int {ι : Type*} [Fintype ι] (p : ι → ℤ) (y : ι → ℤ) :
    dualObj (ratVec p) (fun i => (y i : ℝ)) = ((y ⬝ᵥ p : ℤ) : ℝ) := by
  unfold dualObj ratVec dotProduct
  push_cast
  rfl

theorem cz_eq {ι S : Type*} [Fintype ι] [Fintype S] (Q : Matrix ι S ℤ) (y : ι → ℤ)
    (z : S → ℤ) : ∑ s, (((y ᵥ* Q) s : ℤ) : ℝ) * (z s : ℝ) = ((y ⬝ᵥ (Q *ᵥ z) : ℤ) : ℝ) := by
  rw [Matrix.dotProduct_mulVec]
  unfold dotProduct
  push_cast
  rfl

end BoxTDIMinMax.Separable.Thm33Aux

open BoxTDIMinMax.Separable.Thm33Aux in
theorem solution {ι S : Type*} [Fintype ι] [Fintype S] [DecidableEq S]
    (phi : S → ℤ → WithTop ℤ) (hphi : ∀ s, DiscConvex (phi s))
    (Q : Matrix ι S ℤ) (p : ι → ℤ)
    (hbox : IsBoxTDI (ratMat Q) (ratVec p))
    (hne : (intPts Q p).Nonempty)
    (hfin : ∀ z ∈ intPts Q p, Phi phi z ≠ ⊤) :
    ((∃ M : ℤ, ∀ z ∈ intPts Q p, (M : WithTop ℤ) ≤ Phi phi z) ↔
        ∃ z ∈ intPts Q p, ∃ y : ι → ℤ, 0 ≤ y ∧ Compatible phi Q z y) ∧
      ((∃ M : ℤ, ∀ z ∈ intPts Q p, (M : WithTop ℤ) ≤ Phi phi z) →
        ∃ v : ℤ,
          IsLeast {w | ∃ z ∈ intPts Q p, w = Phi phi z} (v : WithTop ℤ) ∧
          IsGreatest {w | ∃ z ∈ intPts Q p, ∃ y : ι → ℤ, 0 ≤ y ∧ Compatible phi Q z y ∧
              w = Phi phi z + ((-(y ⬝ᵥ (Q *ᵥ z - p)) : ℤ) : WithTop ℤ)} (v : WithTop ℤ) ∧
          ∃ z ∈ intPts Q p, ∃ y : ι → ℤ, 0 ≤ y ∧ Compatible phi Q z y ∧
            Phi phi z + ((-(y ⬝ᵥ (Q *ᵥ z - p)) : ℤ) : WithTop ℤ) = (v : WithTop ℤ) ∧
            (Finset.univ.filter (fun i => 0 < y i)).card ≤ 2 * Fintype.card S) := by
  -- Phi of a point of `R̈` as an integer
  have phiInt : ∀ z ∈ intPts Q p, (((Phi phi z).untopD 0 : ℤ) : WithTop ℤ) = Phi phi z :=
    fun z hz => untop _ (hfin z hz)
  -- dual-value bound from weak duality (Lemma 3.2), in integer form
  have weak : ∀ z₀ ∈ intPts Q p, ∀ y₀ : ι → ℤ, 0 ≤ y₀ → Compatible phi Q z₀ y₀ →
      ∀ z ∈ intPts Q p, (Phi phi z₀).untopD 0 - y₀ ⬝ᵥ (Q *ᵥ z₀ - p) ≤ (Phi phi z).untopD 0 := by
    intro z₀ hz₀ y₀ hy₀ hc z hz
    have h := lemma_3_2 phi hphi Q p z₀ hz₀ y₀ hy₀ hc z hz
    rw [← phiInt z₀ hz₀, ← phiInt z hz] at h
    have h' : (Phi phi z₀).untopD 0 ≤ (Phi phi z).untopD 0 + y₀ ⬝ᵥ (Q *ᵥ z₀ - p) := by
      exact_mod_cast h
    linarith
  -- main construction under boundedness
  have main : (∃ M : ℤ, ∀ z ∈ intPts Q p, (M : WithTop ℤ) ≤ Phi phi z) →
      ∃ zStar ∈ intPts Q p, (∀ z ∈ intPts Q p, Phi phi zStar ≤ Phi phi z) ∧
        ∃ y : ι → ℤ, 0 ≤ y ∧ Compatible phi Q zStar y ∧ y ⬝ᵥ (Q *ᵥ zStar - p) = 0 ∧
          (Finset.univ.filter (fun i => 0 < y i)).card ≤ 2 * Fintype.card S := by
    rintro ⟨M, hM⟩
    -- a Φ-minimizer exists
    classical
    obtain ⟨v, ⟨zStar, hzStar, hv⟩, hvmin⟩ := Int.exists_least_of_bdd
      (P := fun n : ℤ => ∃ z ∈ intPts Q p, (Phi phi z).untopD 0 = n)
      ⟨M, fun n ⟨z, hz, hn⟩ => by
        have := hM z hz
        rw [← phiInt z hz] at this
        rw [← hn]; exact_mod_cast this⟩
      (let ⟨z, hz⟩ := hne; ⟨_, z, hz, rfl⟩)
    have hmin : ∀ z ∈ intPts Q p, Phi phi zStar ≤ Phi phi z := by
      intro z hz
      rw [← phiInt z hz, ← phiInt zStar hzStar, hv]
      exact_mod_cast hvmin _ ⟨z, hz, rfl⟩
    refine ⟨zStar, hzStar, hmin, ?_⟩
    have fin0 : ∀ s, phi s (zStar s) ≠ ⊤ := fun s =>
      WithTop.sum_ne_top.mp (hfin zStar hzStar) s (Finset.mem_univ s)
    -- Claim 3.4 and Theorem 2.12
    have h29 := claim_3_4 phi hphi Q p hfin zStar hzStar hmin
    set lo : S → EReal := fun s => lowerSlope (phi s) (zStar s) with hlo_def
    set up : S → EReal := fun s => upperSlope (phi s) (zStar s) with hup_def
    have hlo : ∀ s, lo s = ⊥ ∨ ∃ k : ℤ, lo s = ((k : ℝ) : EReal) := by
      intro s
      simp only [hlo_def, lowerSlope]
      split_ifs
      · exact Or.inl rfl
      · exact Or.inr ⟨_, rfl⟩
    have hup : ∀ s, up s = ⊤ ∨ ∃ k : ℤ, up s = ((k : ℝ) : EReal) := by
      intro s
      simp only [hup_def, upperSlope]
      split_ifs
      · exact Or.inl rfl
      · exact Or.inr ⟨_, rfl⟩
    have hlu : ∀ s, lo s ≤ up s := by
      intro s
      simp only [hlo_def, hup_def, lowerSlope, upperSlope]
      split_ifs with h1 h2 h2
      · exact bot_le
      · exact bot_le
      · exact le_top
      · have hc := (hphi s).1 (zStar s) (fin0 s)
        rw [← untop _ (fin0 s), ← untop _ h1, ← untop _ h2] at hc
        have hc' : (phi s (zStar s)).untopD 0 + (phi s (zStar s)).untopD 0 ≤
            (phi s (zStar s - 1)).untopD 0 + (phi s (zStar s + 1)).untopD 0 := by
          exact_mod_cast hc
        have : (phi s (zStar s)).untopD 0 - (phi s (zStar s - 1)).untopD 0 ≤
            (phi s (zStar s + 1)).untopD 0 - (phi s (zStar s)).untopD 0 := by linarith
        exact_mod_cast this
    obtain ⟨y0, hy0, hbd, hcs⟩ :=
      (theorem_2_12 Q p hbox zStar hzStar lo up hlo hup hlu).mpr h29
    -- compatibility of any `y` with `y Q = y0 Q`
    have compat : ∀ y : ι → ℤ, y ᵥ* Q = y0 ᵥ* Q → Compatible phi Q zStar y := by
      intro y hyQ s
      rw [hyQ]
      obtain ⟨hl, hu⟩ := hbd s
      refine ⟨fin0 s, ?_, ?_⟩
      · by_cases h1 : phi s (zStar s - 1) = ⊤
        · rw [h1]; simp
        · simp only [hlo_def, lowerSlope, if_neg h1] at hl
          rw [← untop _ (fin0 s), ← untop _ h1]
          have : (phi s (zStar s)).untopD 0 - (phi s (zStar s - 1)).untopD 0 ≤
              (y0 ᵥ* Q) s := by exact_mod_cast hl
          exact_mod_cast (show (phi s (zStar s)).untopD 0 ≤
            (phi s (zStar s - 1)).untopD 0 + (y0 ᵥ* Q) s by linarith)
      · by_cases h1 : phi s (zStar s + 1) = ⊤
        · rw [h1]; simp
        · simp only [hup_def, upperSlope, if_neg h1] at hu
          rw [← untop _ (fin0 s), ← untop _ h1]
          have : (y0 ᵥ* Q) s ≤
              (phi s (zStar s + 1)).untopD 0 - (phi s (zStar s)).untopD 0 := by
            exact_mod_cast hu
          exact_mod_cast (show (phi s (zStar s)).untopD 0 + (y0 ᵥ* Q) s ≤
            (phi s (zStar s + 1)).untopD 0 by linarith)
    -- sparse integral optimal dual solution (Proposition 2.1 + Cook–Fonlupt–Schrijver)
    have hTDI := proposition_2_1 (ratMat Q) (ratVec p) hbox
    set c : S → ℤ := y0 ᵥ* Q with hc_def
    have hfeas0 : (fun i => (y0 i : ℝ)) ∈ DualFeas (ratMat Q) c :=
      (dualFeas_int Q c y0).mpr ⟨hy0, rfl⟩
    have hbdd : BddAbove (dualObj (ratVec p) '' DualFeas (ratMat Q) c) := by
      refine ⟨∑ s, (c s : ℝ) * (zStar s : ℝ), ?_⟩
      rintro _ ⟨y', hy', rfl⟩
      exact dualObj_le Q p c zStar hzStar y' hy'
    obtain ⟨y, hyF, hyopt, hcard⟩ :=
      cook_fonlupt_schrijver Q (ratVec p) hTDI c ⟨_, hfeas0⟩ hbdd
    obtain ⟨hy0', hyQ⟩ := (dualFeas_int Q c y).mp hyF
    refine ⟨y, hy0', compat y hyQ, ?_, hcard⟩
    -- complementary slackness for `y`
    have e1 := hyopt _ hfeas0
    have e2 := dualObj_le Q p c zStar hzStar _ hyF
    rw [dualObj_int, dualObj_int] at e1
    rw [dualObj_int] at e2
    have hcz : ∀ w : ι → ℤ, w ᵥ* Q = c →
        ∑ s, (c s : ℝ) * (zStar s : ℝ) = ((w ⬝ᵥ (Q *ᵥ zStar) : ℤ) : ℝ) := by
      intro w hw
      rw [← cz_eq Q w zStar, hw]
    rw [hcz y hyQ] at e2
    have h0 : y0 ⬝ᵥ p = y0 ⬝ᵥ (Q *ᵥ zStar) := by
      rw [dotProduct_sub] at hcs; linarith
    have hyy0 : y0 ⬝ᵥ (Q *ᵥ zStar) = y ⬝ᵥ (Q *ᵥ zStar) := by
      have h1 := hcz y0 rfl
      have h2 := hcz y hyQ
      exact_mod_cast h1.symm.trans h2
    have e1' : y0 ⬝ᵥ p ≤ y ⬝ᵥ p := by exact_mod_cast e1
    have e2' : y ⬝ᵥ p ≤ y ⬝ᵥ (Q *ᵥ zStar) := by exact_mod_cast e2
    rw [dotProduct_sub]
    linarith
  refine ⟨⟨fun hb => ?_, ?_⟩, fun hb => ?_⟩
  · obtain ⟨zStar, hz, -, y, hy, hc, -, -⟩ := main hb
    exact ⟨zStar, hz, y, hy, hc⟩
  · rintro ⟨z₀, hz₀, y₀, hy₀, hc⟩
    refine ⟨(Phi phi z₀).untopD 0 - y₀ ⬝ᵥ (Q *ᵥ z₀ - p), fun z hz => ?_⟩
    rw [← phiInt z hz]
    exact_mod_cast weak z₀ hz₀ y₀ hy₀ hc z hz
  · obtain ⟨zStar, hz, hmin, y, hy, hc, hcs, hcard⟩ := main hb
    have hval : Phi phi zStar + ((-(y ⬝ᵥ (Q *ᵥ zStar - p)) : ℤ) : WithTop ℤ) =
        (((Phi phi zStar).untopD 0 : ℤ) : WithTop ℤ) := by
      rw [hcs, phiInt zStar hz]; simp
    refine ⟨(Phi phi zStar).untopD 0, ⟨⟨zStar, hz, phiInt zStar hz⟩, ?_⟩,
      ⟨⟨zStar, hz, y, hy, hc, hval.symm⟩, ?_⟩, zStar, hz, y, hy, hc, hval, hcard⟩
    · rintro _ ⟨z, hz', rfl⟩
      rw [phiInt zStar hz]
      exact hmin z hz'
    · rintro _ ⟨z, hz', y', hy', hc', rfl⟩
      have h := weak z hz' y' hy' hc' zStar hz
      rw [← phiInt z hz']
      have : (Phi phi z).untopD 0 + -(y' ⬝ᵥ (Q *ᵥ z - p)) ≤ (Phi phi zStar).untopD 0 := by
        linarith
      exact_mod_cast this
