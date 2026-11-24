-- Prove2me | solution 1 for Formalism.DivisionValues.stepBW_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T09:42:38.623516+00:00
-- url     : https://prove2.me/submissions/540646f9-7112-41ea-8144-b0810e790f2b

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_RatHermLcvTwist
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_DivIntoDual
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_BoundsChain
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_JwConj
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_DualMu
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_TheoremDivIneq
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ConjugateWeightLatticeOfGeneral
import Theorems.Thm_Formalism_DivisionValues_ConjugateWeightGram_local_idW
import Theorems.Thm_Formalism_DivisionValues_StepBAux_G_finite
import Theorems.Thm_Formalism_DivisionValues_StepBAux_detRatio_ne
import Theorems.Thm_Formalism_DivisionValues_StepBAux_lidx_congr
import Theorems.Thm_Formalism_DivisionValues_StepBAux_matLat_lattice
import Theorems.Thm_Formalism_DivisionValues_StepBAux_supp_add
import Theorems.Thm_Formalism_DivisionValues_StepBAux_supp_conj
import Theorems.Thm_Formalism_DivisionValues_StepBAux_supp_sum


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder
noncomputable section
open Formalism Formalism.DivisionValues
open RationalHermitianForm
open StepBAux ConjugateWeightGram
namespace Formalism.DivisionValues
theorem _root_.solution (hPF : ProdFormula) (hLB : LcvBasis) (hIC : IdxChange) (hV : ValBasic)
    (hIm : ImageLcv) (hIL : IdxLcv) (hRH : RatHermLcv) (hJw : JwGramW) (hFC : FinsumConj)
    (hLoc : LocBasisEx) : StepBW := by
  intro K _ _ _ _ K0 hK0 v0 hv0 D XE hXE Tup μ0 μ hμc hμfin XQ hXQ abelian₂ hLam ι hι J _ d XW hXW M hM
    HT XT hHT0 hHTw T hT θ hθ κ hκ ρ ρr hρ hρ1 hρpos hρv hdetAll hdetV0 G e he hG hR R hRlat hRloc
  classical
  have hlw : ∀ w : HeightOneSpectrum (𝓞 K), lw (conjPl w) = lw w := fun w => (hV K w).2.2.1
  have hΛ0 : Submodule.IsLattice K (matLat (ι μ0) (abelian₂ μ0)) :=
    matLat_lattice _ (hι μ0) _ (hLam μ0)
  have hA0 : ∀ j, Submodule.IsLattice K (matLat (θ j μ0) (T j μ0)) := fun j =>
    matLat_lattice _ (hθ j μ0) _ (hT j μ0)
  have hXT : ∀ j t v, IsUnit (XT j t v).det := fun j t v => (hHTw j t).1 v
  choose f hf using fun j t w => hLoc K (d j) (T j t) (hT j t) w

  have hloc : ∀ w : HeightOneSpectrum (𝓞 K),
      idx w (matLat (ι μ0) (abelian₂ μ0)) R + idx (conjPl w) (matLat (ι μ0) (abelian₂ μ0)) R =
        vw w (G (μ w) w) - vw w (G μ0 w) + ∑ j, ((idx w (M j) (matLat (θ j (μ w)) (T j (μ w))) -
            idx w (M j) (matLat (θ j μ0) (T j μ0))) +
          (idx (conjPl w) (M j) (matLat (θ j (μ w)) (T j (μ w))) -
            idx (conjPl w) (M j) (matLat (θ j μ0) (T j μ0))) +
          (jw (HT j (μ w)) w (T j (μ w)) - jw (HT j μ0) w (T j μ0))) := by
    intro w
    have hRc := hRloc (conjPl w)
    rw [hμc] at hRc
    have hx1 : idx w (matLat (ι μ0) (abelian₂ μ0)) R =
        idx w (matLat (ι μ0) (abelian₂ μ0)) (matLat (ι (μ w)) (abelian₂ (μ w))) :=
      lidx_congr _ _ _ _ _ rfl (hRloc w)
    have hx2 : idx (conjPl w) (matLat (ι μ0) (abelian₂ μ0)) R =
        idx (conjPl w) (matLat (ι μ0) (abelian₂ μ0)) (matLat (ι (μ w)) (abelian₂ (μ w))) :=
      lidx_congr _ _ _ _ _ rfl hRc
    rw [hx1, hx2]
    exact local_idW hV hIC hJw v0 hv0 D XE hXE (XQ μ0) (XQ (μ w)) (hXQ μ0) (hXQ (μ w))
      (abelian₂ μ0) (abelian₂ (μ w)) (hLam (μ w)) (ι μ0) (ι (μ w)) (hι μ0) (hι (μ w)) J d XW hXW M hM
      (fun j => HT j μ0) (fun j => HT j (μ w)) (fun j => XT j μ0) (fun j => XT j (μ w))
      (fun j => hHTw j μ0) (fun j => hHTw j (μ w)) (fun j => T j μ0) (fun j => T j (μ w))
      (fun j => hT j μ0) (fun j => hT j (μ w)) (fun j => θ j μ0) (fun j => θ j (μ w))
      (fun j => hθ j μ0) (fun j => hθ j (μ w)) (κ v0) (ρr (μ w)) (hκ v0) (ρ (μ w)) (hρ (μ w))
      (hρpos (μ w)) w (hρv w) (hdetAll v0) (hdetV0 (μ w)) (G μ0 w) (G (μ w) w) (e μ0 w)
      (e (μ w) w) (he μ0 w) (he (μ w) w) (hG μ0 w) (hG (μ w) w) (fun j => f j μ0 w)
      (fun j => f j (μ w) w) (fun j => hf j μ0 w) (fun j => hf j (μ w) w)

  have hFeq : ∀ w : HeightOneSpectrum (𝓞 K),
      lw w * ((vw w (G (μ w) w) : ℝ) + ∑ j,
        ((idx w (M j) (matLat (θ j (μ w)) (T j (μ w))) : ℝ) +
         (idx (conjPl w) (M j) (matLat (θ j (μ w)) (T j (μ w))) : ℝ) +
         (jw (HT j (μ w)) w (T j (μ w)) : ℝ))) =
      lw w * (idx w (matLat (ι μ0) (abelian₂ μ0)) R : ℝ) +
        lw (conjPl w) * (idx (conjPl w) (matLat (ι μ0) (abelian₂ μ0)) R : ℝ) +
        lw w * (vw w (G μ0 w) : ℝ) +
        ∑ j, (lw w * (idx w (M j) (matLat (θ j μ0) (T j μ0)) : ℝ) +
          lw (conjPl w) * (idx (conjPl w) (M j) (matLat (θ j μ0) (T j μ0)) : ℝ) +
          lw w * (jw (HT j μ0) w (T j μ0) : ℝ)) := by
    intro w
    have hZ : vw w (G (μ w) w) + ∑ j, (idx w (M j) (matLat (θ j (μ w)) (T j (μ w))) +
          idx (conjPl w) (M j) (matLat (θ j (μ w)) (T j (μ w))) + jw (HT j (μ w)) w (T j (μ w))) =
        idx w (matLat (ι μ0) (abelian₂ μ0)) R + idx (conjPl w) (matLat (ι μ0) (abelian₂ μ0)) R +
          vw w (G μ0 w) + ∑ j, (idx w (M j) (matLat (θ j μ0) (T j μ0)) +
            idx (conjPl w) (M j) (matLat (θ j μ0) (T j μ0)) + jw (HT j μ0) w (T j μ0)) := by
      have h := hloc w
      have hs : ∑ j, (idx w (M j) (matLat (θ j (μ w)) (T j (μ w))) +
            idx (conjPl w) (M j) (matLat (θ j (μ w)) (T j (μ w))) +
            jw (HT j (μ w)) w (T j (μ w))) =
          ∑ j, ((idx w (M j) (matLat (θ j (μ w)) (T j (μ w))) -
              idx w (M j) (matLat (θ j μ0) (T j μ0))) +
            (idx (conjPl w) (M j) (matLat (θ j (μ w)) (T j (μ w))) -
              idx (conjPl w) (M j) (matLat (θ j μ0) (T j μ0))) +
            (jw (HT j (μ w)) w (T j (μ w)) - jw (HT j μ0) w (T j μ0))) +
          ∑ j, (idx w (M j) (matLat (θ j μ0) (T j μ0)) +
            idx (conjPl w) (M j) (matLat (θ j μ0) (T j μ0)) + jw (HT j μ0) w (T j μ0)) := by
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun j _ => by ring
      linarith
    have hZR : ((vw w (G (μ w) w) : ℤ) : ℝ) + ∑ j,
        ((idx w (M j) (matLat (θ j (μ w)) (T j (μ w))) : ℝ) +
         (idx (conjPl w) (M j) (matLat (θ j (μ w)) (T j (μ w))) : ℝ) +
         (jw (HT j (μ w)) w (T j (μ w)) : ℝ)) =
        (idx w (matLat (ι μ0) (abelian₂ μ0)) R : ℝ) + (idx (conjPl w) (matLat (ι μ0) (abelian₂ μ0)) R : ℝ) +
          (vw w (G μ0 w) : ℝ) + ∑ j, ((idx w (M j) (matLat (θ j μ0) (T j μ0)) : ℝ) +
            (idx (conjPl w) (M j) (matLat (θ j μ0) (T j μ0)) : ℝ) +
            (jw (HT j μ0) w (T j μ0) : ℝ)) := by
      exact_mod_cast hZ
    rw [hlw w, hZR]
    simp only [mul_add, Finset.mul_sum]

  have sx := (hIL K D XE hXE _ R hΛ0 hRlat).1
  have sx' := supp_conj hV _ sx
  have sa := G_finite hV hIC hLB hPF v0 hv0 D (XQ μ0) (hXQ μ0) (abelian₂ μ0) (hLam μ0) (G μ0) (e μ0)
    (he μ0) (hG μ0)
  have sb : ∀ j, (Function.support fun w : HeightOneSpectrum (𝓞 K) =>
      lw w * (idx w (M j) (matLat (θ j μ0) (T j μ0)) : ℝ)).Finite := fun j =>
    (hIL K (d j) (XW j) (hXW j) (M j) _ (hM j) (hA0 j)).1
  have sb' : ∀ j, (Function.support fun w : HeightOneSpectrum (𝓞 K) =>
      lw (conjPl w) * (idx (conjPl w) (M j) (matLat (θ j μ0) (T j μ0)) : ℝ)).Finite := fun j =>
    supp_conj hV _ (sb j)
  have sc : ∀ j, (Function.support fun w : HeightOneSpectrum (𝓞 K) =>
      lw w * (jw (HT j μ0) w (T j μ0) : ℝ)).Finite := fun j =>
    (hRH K K0 hK0 (d j) (HT j μ0) (XT j μ0) (hHT0 j) (T j μ0) (hT j μ0)).1
  have sin : ∀ j, (Function.support fun w : HeightOneSpectrum (𝓞 K) =>
      lw w * (idx w (M j) (matLat (θ j μ0) (T j μ0)) : ℝ) +
        lw (conjPl w) * (idx (conjPl w) (M j) (matLat (θ j μ0) (T j μ0)) : ℝ) +
        lw w * (jw (HT j μ0) w (T j μ0) : ℝ)).Finite := fun j =>
    supp_add _ _ (supp_add _ _ (sb j) (sb' j)) (sc j)
  have sJ := supp_sum (fun j (w : HeightOneSpectrum (𝓞 K)) =>
      lw w * (idx w (M j) (matLat (θ j μ0) (T j μ0)) : ℝ) +
        lw (conjPl w) * (idx (conjPl w) (M j) (matLat (θ j μ0) (T j μ0)) : ℝ) +
        lw w * (jw (HT j μ0) w (T j μ0) : ℝ)) sin
  have s12 := supp_add _ _ sx sx'
  have s123 := supp_add _ _ s12 sa
  have sAll := supp_add _ _ s123 sJ
  refine ⟨sAll.subset ?_, ?_⟩
  · intro w hw
    simp only [Function.mem_support] at hw ⊢
    rwa [hFeq w] at hw

  have hsumF := finsum_congr hFeq
  rw [finsum_add_distrib s123 sJ, finsum_add_distrib s12 sa, finsum_add_distrib sx sx',
    finsum_sum_comm _ _ (fun j _ => sin j)] at hsumF
  have hcx : (∑ᶠ w, lw (conjPl w) * (idx (conjPl w) (matLat (ι μ0) (abelian₂ μ0)) R : ℝ)) =
      ∑ᶠ w, lw w * (idx w (matLat (ι μ0) (abelian₂ μ0)) R : ℝ) :=
    hFC K (fun w => lw w * (idx w (matLat (ι μ0) (abelian₂ μ0)) R : ℝ))
  have hcb : ∑ j, (∑ᶠ w, (lw w * (idx w (M j) (matLat (θ j μ0) (T j μ0)) : ℝ) +
        lw (conjPl w) * (idx (conjPl w) (M j) (matLat (θ j μ0) (T j μ0)) : ℝ) +
        lw w * (jw (HT j μ0) w (T j μ0) : ℝ))) =
      ∑ j, (2 * ∑ᶠ w, lw w * (idx w (M j) (matLat (θ j μ0) (T j μ0)) : ℝ) +
        ∑ᶠ w, lw w * (jw (HT j μ0) w (T j μ0) : ℝ)) := by
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [finsum_add_distrib (supp_add _ _ (sb j) (sb' j)) (sc j),
      finsum_add_distrib (sb j) (sb' j),
      hFC K (fun w => lw w * (idx w (M j) (matLat (θ j μ0) (T j μ0)) : ℝ))]
    ring

  have hI1 := (hIL K D XE hXE _ R hΛ0 hRlat).2
  have hI2 := hIm K D (XQ μ0) XE (hXQ μ0) hXE (ι μ0) (hι μ0) (abelian₂ μ0) (hLam μ0)
  have hθne : ∀ j v, detRatio (XT j μ0) (XW j) (θ j μ0) v ≠ 0 := fun j v =>
    detRatio_ne (XT j μ0) (XW j) (hXT j μ0) (hXW j) (θ j μ0) (hθ j μ0) v
  have hlogv : ∀ v, Real.log (detRatio (XQ μ0) XE (ι μ0) v) =
      (D : ℝ) * Real.log (κ v) + ∑ j, Real.log (detRatio (XT j μ0) (XW j) (θ j μ0) v) := by
    intro v
    rw [hdetAll v, Real.log_mul (pow_ne_zero _ (hκ v).ne')
      (Finset.prod_ne_zero_iff.mpr fun j _ => hθne j v), Real.log_pow,
      Real.log_prod (fun j _ => hθne j v)]
  have hlogsum : ∑ v, Real.log (detRatio (XQ μ0) XE (ι μ0) v) =
      (D : ℝ) * ∑ v, Real.log (κ v) +
        ∑ j, ∑ v, Real.log (detRatio (XT j μ0) (XW j) (θ j μ0) v) := by
    rw [Finset.sum_congr rfl (fun v _ => hlogv v), Finset.sum_add_distrib, ← Finset.mul_sum,
      Finset.sum_comm]
  have hN : (finrank ℚ K : ℝ) = 2 * (Formalism.HN.nPl K : ℝ) := by
    rw [IsTotallyComplex.finrank, Formalism.HN.nPl,
      NumberField.InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces,
      IsTotallyComplex.nrRealPlaces_eq_zero, zero_add]
    push_cast; ring
  have hmean : (2 / (finrank ℚ K : ℝ)) * ((D : ℝ) * ∑ v, Real.log (κ v)) = (D : ℝ) * meanLog κ := by
    rw [meanLog, hN]
    rcases eq_or_ne (Formalism.HN.nPl K : ℝ) 0 with h0 | h0
    · rw [h0]; simp
    · field_simp
  have hθj : ∀ j, (2 / (finrank ℚ K : ℝ)) *
      ∑ v, Real.log (detRatio (XT j μ0) (XW j) (θ j μ0) v) =
      lcv (XW j) (M j) + (2 * ∑ᶠ w, lw w * (idx w (M j) (matLat (θ j μ0) (T j μ0)) : ℝ) +
        ∑ᶠ w, lw w * (jw (HT j μ0) w (T j μ0) : ℝ)) := by
    intro j
    have e1 := hIm K (d j) (XT j μ0) (XW j) (hXT j μ0) (hXW j) (θ j μ0) (hθ j μ0) (T j μ0)
      (hT j μ0)
    have e2 := (hIL K (d j) (XW j) (hXW j) (M j) _ (hM j) (hA0 j)).2
    have e3 := (hRH K K0 hK0 (d j) (HT j μ0) (XT j μ0) (hHT0 j) (T j μ0) (hT j μ0)).2
    linarith
  have hθsum : (2 / (finrank ℚ K : ℝ)) *
      ∑ j, ∑ v, Real.log (detRatio (XT j μ0) (XW j) (θ j μ0) v) =
      ∑ j, lcv (XW j) (M j) + ∑ j, (2 * ∑ᶠ w, lw w * (idx w (M j) (matLat (θ j μ0) (T j μ0)) : ℝ) +
        ∑ᶠ w, lw w * (jw (HT j μ0) w (T j μ0) : ℝ)) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => hθj j
  rw [hlogsum, mul_add] at hI2
  rw [hsumF, hcx, hcb]
  linarith
end Formalism.DivisionValues
