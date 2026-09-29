-- Prove2me | solution 1 for CuspForm.HasNebentypus.apply_mul_padicToAdelic_centralGL_eq_of_isAdelicLiftOfGamma1
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/79cc315e-1d5e-5d25-9af1-e42e5968e070

import Definitions.Def_CuspForm_AdelicLiftGamma1
import Definitions.Def_CuspForm_PrimitiveFormGamma1
import Definitions.Def_LocalNewvector_ConductorDatum
import Definitions.Def_AdelicDock_LocalEmbedding
import Theorems.Thm_NumberField_AdelicLevel_exists_globalPoints_mul_mem_levelOne_rat
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CuspForm_HasNebentypus_apply_mul_padicToAdelic_centralGL_eq_of_isAdelicLiftOfGamma1

set_option autoImplicit false

noncomputable section

open NumberField AdelicDock IsDedekindDomain

namespace CentralNebentypus

open NumberField NumberField.AdelicLevel AdelicDock AutomorphicForm IsDedekindDomain

section GlobalPointsLemmas

theorem isReal_rat_infinitePlace (v : InfinitePlace ℚ) : v.IsReal := IsTotallyReal.isReal v

def ratArchHom : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ) →* GL (Fin 2) ℝ :=
  (Matrix.GeneralLinearGroup.map
    (InfinitePlace.Completion.ringEquivRealOfIsReal (isReal_rat_infinitePlace default)).toRingHom).comp
    ((archComponent ℚ default).comp (glArch (𝓞 ℚ) ℚ))

theorem ratArchHom_apply (g : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) :
    ratArchHom g = LanglandsTunnell.ratArchGL2 g := rfl

theorem ratArch_mul (g g' : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) :
    LanglandsTunnell.ratArchGL2 (g * g')
      = LanglandsTunnell.ratArchGL2 g * LanglandsTunnell.ratArchGL2 g' := by
  rw [← ratArchHom_apply, ← ratArchHom_apply, ← ratArchHom_apply, map_mul]

theorem ratArch_inv (g : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) :
    LanglandsTunnell.ratArchGL2 g⁻¹ = (LanglandsTunnell.ratArchGL2 g)⁻¹ := by
  rw [← ratArchHom_apply, ← ratArchHom_apply, map_inv]

theorem ratArch_eq_one_of_glArch_eq_one {u : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)} (hu : glArch (𝓞 ℚ) ℚ u = 1) :
    LanglandsTunnell.ratArchGL2 u = 1 := by
  unfold LanglandsTunnell.ratArchGL2
  rw [hu, map_one, map_one]

theorem ratArch_finEmbed (u : GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) :
    LanglandsTunnell.ratArchGL2 (finEmbed (𝓞 ℚ) ℚ u) = 1 :=
  ratArch_eq_one_of_glArch_eq_one (glArch_finEmbed (𝓞 ℚ) ℚ u)

theorem ratArch_globalPoints (γ : GL (Fin 2) ℚ) :
    LanglandsTunnell.ratArchGL2 (globalPoints (𝓞 ℚ) ℚ γ) = Matrix.GeneralLinearGroup.map (Rat.castHom ℝ) γ := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  change ((InfinitePlace.Completion.ringEquivRealOfIsReal (isReal_rat_infinitePlace default)).toRingHom.comp
      ((archEval ℚ default).comp ((adeleArch (𝓞 ℚ) ℚ).comp (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ)))))
      ((γ : Matrix (Fin 2) (Fin 2) ℚ) i j) = (Rat.castHom ℝ) ((γ : Matrix (Fin 2) (Fin 2) ℚ) i j)
  rw [eq_ratCast, eq_ratCast]

theorem glFin_globalPoints_apply (γ : GL (Fin 2) ℚ) (i j : Fin 2) :
    (glFin (𝓞 ℚ) ℚ (globalPoints (𝓞 ℚ) ℚ γ) : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) i j
      = algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) ((γ : Matrix (Fin 2) (Fin 2) ℚ) i j) := rfl

end GlobalPointsLemmas

theorem gl_ext_of_arch_fin {x y : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)}
    (h₁ : glArch (𝓞 ℚ) ℚ x = glArch (𝓞 ℚ) ℚ y) (h₂ : glFin (𝓞 ℚ) ℚ x = glFin (𝓞 ℚ) ℚ y) : x = y := by
  refine Units.ext (Matrix.ext fun a b => Prod.ext ?_ ?_)
  · exact congrArg (fun g : GL (Fin 2) (InfiniteAdeleRing ℚ) => (g : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing ℚ)) a b) h₁
  · exact congrArg
      (fun g : GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ) => (g : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) a b) h₂

theorem finEmbed_mul_comm_of_glFin_eq_one {h : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)} (hh : glFin (𝓞 ℚ) ℚ h = 1)
    (u : GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) :
    finEmbed (𝓞 ℚ) ℚ u * h = h * finEmbed (𝓞 ℚ) ℚ u := by
  refine gl_ext_of_arch_fin ?_ ?_
  · rw [map_mul, map_mul, glArch_finEmbed, one_mul, mul_one]
  · rw [map_mul, map_mul, glFin_finEmbed, hh, one_mul, mul_one]

def archPart (γ : GL (Fin 2) ℚ) : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ) :=
  globalPoints (𝓞 ℚ) ℚ γ * (finEmbed (𝓞 ℚ) ℚ (glFin (𝓞 ℚ) ℚ (globalPoints (𝓞 ℚ) ℚ γ)))⁻¹

theorem glFin_archPart (γ : GL (Fin 2) ℚ) : glFin (𝓞 ℚ) ℚ (archPart γ) = 1 := by
  rw [archPart, map_mul, map_inv, glFin_finEmbed, mul_inv_cancel]

theorem ratArch_archPart (γ : GL (Fin 2) ℚ) :
    LanglandsTunnell.ratArchGL2 (archPart γ) = Matrix.GeneralLinearGroup.map (Rat.castHom ℝ) γ := by
  rw [archPart, ratArch_mul, ratArch_inv, ratArch_finEmbed, inv_one, mul_one, ratArch_globalPoints]

theorem globalPoints_eq_archPart_mul (γ : GL (Fin 2) ℚ) :
    globalPoints (𝓞 ℚ) ℚ γ = archPart γ * finEmbed (𝓞 ℚ) ℚ (glFin (𝓞 ℚ) ℚ (globalPoints (𝓞 ℚ) ℚ γ)) := by
  rw [archPart, inv_mul_cancel_right]

theorem exists_eq_globalPoints_mul_mul_finEmbed_of_mem_finiteLevelOne {M : ℕ} (hM : M ≠ 0)
    (x : AdelicGL2 (𝓞 ℚ) ℚ) :
    ∃ (γ : GL (Fin 2) ℚ) (h : AdelicGL2 (𝓞 ℚ) ℚ)
      (u : GL (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ)),
      AdelicLevel.glFin (𝓞 ℚ) ℚ h = 1 ∧
        LanglandsTunnell.ratArchGL2 h ∈ Matrix.GLPos (Fin 2) ℝ ∧
          u ∈ AdelicLevel.finiteLevelOne (𝓞 ℚ) ℚ (AdelicDock.ratLevel M) ∧
            x = globalPoints (𝓞 ℚ) ℚ γ * h * AdelicDock.finEmbed (𝓞 ℚ) ℚ u := by
  obtain ⟨γ', hlev, hpos⟩ :=
    AdelicLevel.exists_globalPoints_mul_mem_levelOne_rat (AdelicDock.ratLevel_ne_bot hM) x
  set y : AdelicGL2 (𝓞 ℚ) ℚ := globalPoints (𝓞 ℚ) ℚ γ' * x with hy
  set u : GL (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ) :=
    AdelicLevel.glFin (𝓞 ℚ) ℚ y with hu
  refine ⟨γ'⁻¹, y * (AdelicDock.finEmbed (𝓞 ℚ) ℚ u)⁻¹, u, ?_, ?_, ?_, ?_⟩
  · rw [map_mul, map_inv, AdelicDock.glFin_finEmbed, mul_inv_cancel]
  · have hy_pos : LanglandsTunnell.ratArchGL2 y ∈ Matrix.GLPos (Fin 2) ℝ :=
      hpos default (IsTotallyReal.isReal default)
    rw [← map_inv, ratArch_mul, ratArch_finEmbed]
    simpa using hy_pos
  · exact (AdelicLevel.mem_levelOne_iff).mp hlev
  · rw [map_inv, hy]
    group

theorem σ_apply_of_det_pos {g : GL (Fin 2) ℝ} (hg : 0 < (g.det : ℝ)) (z : ℂ) :
    UpperHalfPlane.σ g z = z := by
  rw [UpperHalfPlane.σ, if_pos hg]
  rfl

theorem natGenerator_padicPlace (p : ℕ) [Fact p.Prime] :
    Rat.HeightOneSpectrum.natGenerator (R := 𝓞 ℚ) (padicPlace p) = p :=
  congrArg Subtype.val
    ((Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).apply_symm_apply ⟨p, Fact.out⟩)

theorem eq_padicPlace_natGenerator (v : HeightOneSpectrum (𝓞 ℚ)) :
    haveI : Fact (Rat.HeightOneSpectrum.natGenerator v).Prime :=
      ⟨Rat.HeightOneSpectrum.prime_natGenerator v⟩
    v = padicPlace (Rat.HeightOneSpectrum.natGenerator v) := by
  haveI : Fact (Rat.HeightOneSpectrum.natGenerator v).Prime :=
    ⟨Rat.HeightOneSpectrum.prime_natGenerator v⟩
  refine ((Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).symm_apply_apply v).symm.trans ?_
  exact congrArg _ (Subtype.ext rfl)

theorem algebraMap_intCast_apply_padicPlace_eq (p : ℕ) [Fact p.Prime] (n : ℤ) :
    (algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) (n : ℚ)) (padicPlace p)
      = padicRingEquiv p ((n : ℤ_[p]) : ℚ_[p]) := by
  have hL : (algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) (n : ℚ)) (padicPlace p) =
      (n : (padicPlace p).adicCompletion ℚ) := by
    change ((algebraMap ℚ ((padicPlace p).adicCompletion ℚ)).comp (Int.castRingHom ℚ)) n = _
    exact eq_intCast _ n
  have hR : padicRingEquiv p ((n : ℤ_[p]) : ℚ_[p]) = (n : (padicPlace p).adicCompletion ℚ) := by
    rw [PadicInt.coe_intCast, map_intCast]
  exact hL.trans hR.symm

theorem isLevelZeroMatrix_mapMatrix_of_int_entries {N : ℕ} (hN : N ≠ 0)
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

theorem map_algebraMap_mem_finiteLevelZero {N : ℕ} (hN : N ≠ 0) (δ : GL (Fin 2) ℚ)
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

theorem glFin_globalPoints_eq_map (δ : GL (Fin 2) ℚ) :
    glFin (𝓞 ℚ) ℚ (globalPoints (𝓞 ℚ) ℚ δ)
      = Matrix.GeneralLinearGroup.map (algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ)) δ := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  rw [glFin_globalPoints_apply]
  rfl

theorem mapGL_entry_int (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) (a b : Fin 2) :
    ∃ n : ℤ, ((Matrix.SpecialLinearGroup.mapGL ℚ γ : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) a b = n :=
  ⟨γ a b, by simp [Matrix.SpecialLinearGroup.mapGL]⟩

theorem mapGL_lowerLeft_of_mem_Gamma0 {N : ℕ} {γ : Matrix.SpecialLinearGroup (Fin 2) ℤ}
    (hγ : γ ∈ CongruenceSubgroup.Gamma0 N) :
    ∃ m : ℤ, ((Matrix.SpecialLinearGroup.mapGL ℚ γ : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) 1 0 = (N : ℚ) * m := by
  obtain ⟨m, hm⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd (γ 1 0) N).mp (CongruenceSubgroup.Gamma0_mem.mp hγ)
  refine ⟨m, ?_⟩
  simp [Matrix.SpecialLinearGroup.mapGL, hm]

theorem glFin_globalPoints_mapGL_mem_finiteLevelZero {N : ℕ} (hN : N ≠ 0) {γ : Matrix.SpecialLinearGroup (Fin 2) ℤ}
    (hγ : γ ∈ CongruenceSubgroup.Gamma0 N) :
    glFin (𝓞 ℚ) ℚ (globalPoints (𝓞 ℚ) ℚ (Matrix.SpecialLinearGroup.mapGL ℚ γ)) ∈ finiteLevelZero (𝓞 ℚ) ℚ (ratLevel N) := by
  rw [glFin_globalPoints_eq_map]
  refine map_algebraMap_mem_finiteLevelZero hN _ (mapGL_entry_int γ) ?_
    (mapGL_lowerLeft_of_mem_Gamma0 hγ) ?_
  · rw [← map_inv]
    exact mapGL_entry_int γ⁻¹
  · rw [← map_inv]
    exact mapGL_lowerLeft_of_mem_Gamma0 (Subgroup.inv_mem _ hγ)

theorem map_castHom_mapGL (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) :
    Matrix.GeneralLinearGroup.map (Rat.castHom ℝ) (Matrix.SpecialLinearGroup.mapGL ℚ γ)
      = Matrix.SpecialLinearGroup.mapGL ℝ γ := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  simp [Matrix.SpecialLinearGroup.mapGL]

theorem mapGL_mem_GLPos (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) :
    (Matrix.SpecialLinearGroup.mapGL ℝ γ : GL (Fin 2) ℝ) ∈ Matrix.GLPos (Fin 2) ℝ := by
  rw [Matrix.mem_glpos]
  simp [Matrix.SpecialLinearGroup.mapGL]

theorem valued_det_finComponent_eq_one_of_mem_finiteLevelZero
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

theorem mem_finiteLevelOne_of_lowerRight {N : Ideal (𝓞 ℚ)} {g : GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)}
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

section Central

open LocalNewvector

variable (q : ℕ) [Fact q.Prime]

theorem padicGL_centralGL_apply (u : ℤ_[q]ˣ) (i j : Fin 2) :
    ((padicGL q (centralGL q (Units.map PadicInt.Coe.ringHom.toMonoidHom u)) :
        GL (Fin 2) ((padicPlace q).adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) ((padicPlace q).adicCompletion ℚ)) i j
      = if i = j then padicRingEquiv q ((u : ℤ_[q]) : ℚ_[q]) else 0 := by
  rw [padicGL_apply]
  show padicRingEquiv q ((algebraMap ℚ_[q] (Matrix (Fin 2) (Fin 2) ℚ_[q])) ((u : ℤ_[q]) : ℚ_[q]) i j) = _
  rw [Matrix.algebraMap_matrix_apply]
  split_ifs
  · rfl
  · rw [map_zero]

theorem padicToFinAdelic_centralGL_mem_finiteLevelZero (M : ℕ) (u : ℤ_[q]ˣ) :
    padicToFinAdelic q (centralGL q (Units.map PadicInt.Coe.ringHom.toMonoidHom u))
      ∈ finiteLevelZero (𝓞 ℚ) ℚ (ratLevel M) := by
  have hbody : ∀ u' : ℤ_[q]ˣ, IsLevelZeroMatrix (𝓞 ℚ) ℚ (ratLevel M)
      ((padicToFinAdelic q (centralGL q (Units.map PadicInt.Coe.ringHom.toMonoidHom u'))).val) := by
    intro u'
    refine ⟨fun i j w => ?_, ?_⟩
    · rw [padicToFinAdelic_apply, coe_localEmbed]
      by_cases hw : w = padicPlace q
      · subst hw
        rw [localMat_apply_self, padicGL_centralGL_apply]
        split_ifs
        · exact padicRingEquiv_coe_mem q (u' : ℤ_[q])
        · exact zero_mem _
      · rw [localMat_apply_of_ne (𝓞 ℚ) ℚ (padicPlace q) _ i j hw, Matrix.one_apply]
        split_ifs
        · exact one_mem _
        · exact zero_mem _
    · intro w
      rw [padicToFinAdelic_apply, coe_localEmbed]
      by_cases hw : w = padicPlace q
      · subst hw
        rw [localMat_apply_self, padicGL_centralGL_apply, if_neg (by decide), map_zero]
        exact zero_le'
      · rw [localMat_apply_of_ne (𝓞 ℚ) ℚ (padicPlace q) _ 1 0 hw,
          Matrix.one_apply_ne (by decide), map_zero]
        exact zero_le'
  refine mem_finiteLevelZero_iff.mpr ⟨hbody u, ?_⟩
  have hinv : (padicToFinAdelic q (centralGL q (Units.map PadicInt.Coe.ringHom.toMonoidHom u)))⁻¹
      = padicToFinAdelic q (centralGL q (Units.map PadicInt.Coe.ringHom.toMonoidHom u⁻¹)) := by
    rw [← map_inv, ← map_inv, ← map_inv]
  rw [hinv]
  exact hbody u⁻¹

theorem coe_finComponent (w : HeightOneSpectrum (𝓞 ℚ)) (g : GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) :
    ((finComponent (𝓞 ℚ) ℚ w g) : Matrix (Fin 2) (Fin 2) (w.adicCompletion ℚ))
      = (finAdeleEval (𝓞 ℚ) ℚ w).mapMatrix (g : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) := by
  ext i j
  rw [finComponent_apply, RingHom.mapMatrix_apply, Matrix.map_apply, finAdeleEval_apply]

theorem glEq_of_forall_finComponent_eq {g h : GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)}
    (H : ∀ w : HeightOneSpectrum (𝓞 ℚ), finComponent (𝓞 ℚ) ℚ w g = finComponent (𝓞 ℚ) ℚ w h) :
    g = h := by
  refine Matrix.GeneralLinearGroup.ext fun i j => congrFun (congrFun ?_ i) j
  refine matrix_eq_of_forall_mapMatrix_finAdeleEval_eq (𝓞 ℚ) ℚ fun w => ?_
  rw [← coe_finComponent w g, ← coe_finComponent w h, H w]

theorem padicToFinAdelic_centralGL_mul_comm (u : ℤ_[q]ˣ) (g : GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) :
    padicToFinAdelic q (centralGL q (Units.map PadicInt.Coe.ringHom.toMonoidHom u)) * g
      = g * padicToFinAdelic q (centralGL q (Units.map PadicInt.Coe.ringHom.toMonoidHom u)) := by
  refine glEq_of_forall_finComponent_eq fun w => ?_
  rw [map_mul, map_mul]
  by_cases hw : w = padicPlace q
  · subst hw
    rw [finComponent_padicToFinAdelic_self]
    apply Units.ext
    rw [Units.val_mul, Units.val_mul]
    have hsc : ((padicGL q (centralGL q (Units.map PadicInt.Coe.ringHom.toMonoidHom u)) :
        GL (Fin 2) ((padicPlace q).adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) ((padicPlace q).adicCompletion ℚ))
        = algebraMap ((padicPlace q).adicCompletion ℚ) (Matrix (Fin 2) (Fin 2) ((padicPlace q).adicCompletion ℚ))
            (padicRingEquiv q ((u : ℤ_[q]) : ℚ_[q])) := by
      ext i j
      rw [padicGL_centralGL_apply, Matrix.algebraMap_matrix_apply]
      rfl
    rw [hsc]
    exact Algebra.commutes _ _
  · rw [finComponent_padicToFinAdelic_of_ne _ _ hw, one_mul, mul_one]

end Central

section Reading

open scoped ModularForm

variable {N : ℕ} {ε : DirichletCharacter ℂ N} {F : CuspForm (CongruenceSubgroup.Gamma1 N) 2}
variable {Ψ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ}

theorem glFin_conj_eq_one' (δ : GL (Fin 2) ℚ) {h : AdelicGL2 (𝓞 ℚ) ℚ} (hh : glFin (𝓞 ℚ) ℚ h = 1) :
    glFin (𝓞 ℚ) ℚ ((globalPoints (𝓞 ℚ) ℚ δ)⁻¹ * h * globalPoints (𝓞 ℚ) ℚ δ) = 1 := by
  rw [map_mul, map_mul, hh, mul_one, map_inv, inv_mul_cancel]

theorem slash_eq_smul_of_hasNebentypus (hε : CuspForm.HasNebentypus ε F)
    {γ : Matrix.SpecialLinearGroup (Fin 2) ℤ} (hγ : γ ∈ CongruenceSubgroup.Gamma0 N) :
    (⇑F) ∣[(2 : ℤ)] (Matrix.SpecialLinearGroup.mapGL ℝ γ : GL (Fin 2) ℝ) = ε ((γ 1 1 : ℤ) : ZMod N) • (⇑F) := by
  funext τ
  have hSL : ((⇑F) ∣[(2 : ℤ)] (Matrix.SpecialLinearGroup.mapGL ℝ γ : GL (Fin 2) ℝ)) τ
      = F (γ • τ) * UpperHalfPlane.denom γ τ ^ (-(2 : ℤ)) := ModularForm.SL_slash_apply (k := 2) (⇑F) γ τ
  have hden : UpperHalfPlane.denom γ τ ≠ 0 := UpperHalfPlane.denom_ne_zero γ τ
  rw [ModularGroup.denom_apply] at hden
  rw [hSL, hε γ hγ τ, ModularGroup.denom_apply, Pi.smul_apply, smul_eq_mul]
  have h2 : (((γ 1 0 : ℤ) : ℂ) * (τ : ℂ) + ((γ 1 1 : ℤ) : ℂ)) ^ (2 : ℤ) ≠ 0 := zpow_ne_zero _ hden
  field_simp

theorem apply_mul_finEmbed_eq_of_mem_finiteLevelOne (hε : CuspForm.HasNebentypus ε F)
    (hΨ : CuspForm.IsAdelicLiftOfGamma1 F Ψ)
    {σ : Matrix.SpecialLinearGroup (Fin 2) ℤ} (hσ : σ ∈ CongruenceSubgroup.Gamma0 N)
    {k : GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)}
    (hk : glFin (𝓞 ℚ) ℚ (globalPoints (𝓞 ℚ) ℚ (Matrix.SpecialLinearGroup.mapGL ℚ σ)) * k
      ∈ finiteLevelOne (𝓞 ℚ) ℚ (ratLevel N))
    {X : AdelicGL2 (𝓞 ℚ) ℚ} (hX : glFin (𝓞 ℚ) ℚ X = 1) (hXpos : LanglandsTunnell.ratArchGL2 X ∈ Matrix.GLPos (Fin 2) ℝ) :
    Ψ (X * finEmbed (𝓞 ℚ) ℚ k) = ε ((σ 1 1 : ℤ) : ZMod N) * Ψ X := by
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
  rw [hXk, hΨ.left_inv, hΨ.level_inv _ hk, hΨ.apply_eq Y hYfin hYpos, hYarch, SlashAction.slash_mul,
    slash_eq_smul_of_hasNebentypus hε hσ, ModularForm.smul_slash, Pi.smul_apply, smul_eq_mul,
    σ_apply_of_det_pos ((Matrix.mem_glpos _).mp hXpos), hΨ.apply_eq X hX hXpos]

end Reading

section Compensate

open LocalNewvector

variable (q : ℕ) [hq : Fact q.Prime]

omit hq in

theorem exists_gamma0_lowerRight_eq {M : ℕ} {d : ℤ} (hd : IsCoprime d (M : ℤ)) :
    ∃ σ : Matrix.SpecialLinearGroup (Fin 2) ℤ, σ ∈ CongruenceSubgroup.Gamma0 M ∧ σ 1 1 = d := by
  obtain ⟨x, y, hxy⟩ := hd
  refine ⟨⟨!![x, -y; (M : ℤ), d], by rw [Matrix.det_fin_two_of]; linarith⟩, ?_, rfl⟩
  rw [CongruenceSubgroup.Gamma0_mem]
  show (((M : ℤ) : ℤ) : ZMod M) = 0
  simp

theorem glFin_globalPoints_mul_centralGL_mem_finiteLevelOne {M : ℕ} (hM : M ≠ 0)
    {σ : Matrix.SpecialLinearGroup (Fin 2) ℤ} (hσ : σ ∈ CongruenceSubgroup.Gamma0 M)
    (u : ℤ_[q]ˣ)
    (hdq : ((σ 1 1 : ℤ) : ℤ_[q]) * u - 1 ∈ Ideal.span {(q : ℤ_[q]) ^ M.factorization q})
    (hdM : ((M / q ^ M.factorization q : ℕ) : ℤ) ∣ σ 1 1 - 1) :
    glFin (𝓞 ℚ) ℚ (globalPoints (𝓞 ℚ) ℚ (Matrix.SpecialLinearGroup.mapGL ℚ σ)) *
        padicToFinAdelic q (centralGL q (Units.map PadicInt.Coe.ringHom.toMonoidHom u))
      ∈ finiteLevelOne (𝓞 ℚ) ℚ (ratLevel M) := by
  set k := padicToFinAdelic q (centralGL q (Units.map PadicInt.Coe.ringHom.toMonoidHom u)) with hk
  have hK₀ : glFin (𝓞 ℚ) ℚ (globalPoints (𝓞 ℚ) ℚ (Matrix.SpecialLinearGroup.mapGL ℚ σ)) * k
      ∈ finiteLevelZero (𝓞 ℚ) ℚ (ratLevel M) :=
    mul_mem (glFin_globalPoints_mapGL_mem_finiteLevelZero hM hσ)
      (padicToFinAdelic_centralGL_mem_finiteLevelZero q M u)
  refine mem_finiteLevelOne_of_lowerRight hK₀ fun v => ?_
  rw [coe_sub_apply, coe_one_apply, ← finComponent_apply, map_mul, Units.val_mul, Matrix.mul_apply,
    Fin.sum_univ_two]
  by_cases hv : v = padicPlace q
  ·
    subst hv
    rw [hk, finComponent_padicToFinAdelic_self, padicGL_centralGL_apply, padicGL_centralGL_apply,
      if_neg (by decide), mul_zero, zero_add, if_pos rfl, finComponent_apply, glFin_globalPoints_apply]
    obtain ⟨n, hn⟩ := mapGL_entry_int σ 1 1
    have hn' : n = σ 1 1 := by
      have : ((Matrix.SpecialLinearGroup.mapGL ℚ σ : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) 1 1 = (σ 1 1 : ℚ) := by
        simp [Matrix.SpecialLinearGroup.mapGL]
      exact_mod_cast (hn.symm.trans this)
    rw [hn, algebraMap_intCast_apply_padicPlace_eq q n, ← map_mul, ← map_one (padicRingEquiv q), ← map_sub,
      ← PadicInt.coe_mul, ← PadicInt.coe_one, ← PadicInt.coe_sub, valued_coe_le_idealBound_iff q hM, hn']
    exact hdq
  ·
    rw [hk, finComponent_padicToFinAdelic_of_ne _ _ hv, Units.val_one, Matrix.one_apply_ne (by decide),
      mul_zero, zero_add, Matrix.one_apply_eq, mul_one, finComponent_apply, glFin_globalPoints_apply]
    haveI hℓp : Fact (Rat.HeightOneSpectrum.natGenerator v).Prime := ⟨Rat.HeightOneSpectrum.prime_natGenerator v⟩
    have hne : Rat.HeightOneSpectrum.natGenerator v ≠ q := fun heq =>
      hv <| (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).injective <|
        Subtype.ext <| heq.trans (natGenerator_padicPlace q).symm
    rw [eq_padicPlace_natGenerator v]
    set ℓ := Rat.HeightOneSpectrum.natGenerator v
    obtain ⟨n, hn⟩ := mapGL_entry_int σ 1 1
    have hn' : n = σ 1 1 := by
      have : ((Matrix.SpecialLinearGroup.mapGL ℚ σ : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) 1 1 = (σ 1 1 : ℚ) := by
        simp [Matrix.SpecialLinearGroup.mapGL]
      exact_mod_cast (hn.symm.trans this)
    rw [hn, algebraMap_intCast_apply_padicPlace_eq ℓ n, ← map_one (padicRingEquiv ℓ), ← map_sub,
      ← PadicInt.coe_one, ← PadicInt.coe_sub, valued_coe_le_idealBound_iff ℓ hM, hn']

    have hfacℓ : (M / q ^ M.factorization q).factorization ℓ = M.factorization ℓ := by
      rw [Nat.factorization_ordCompl, Finsupp.erase_ne hne]
    have hdvd : ((ℓ : ℤ) ^ M.factorization ℓ) ∣ σ 1 1 - 1 := by
      refine (Int.natCast_dvd_natCast.mpr ?_ |>.trans (by exact_mod_cast hdM))
      rw [← hfacℓ]
      exact Nat.ordProj_dvd _ _
    obtain ⟨c, hc⟩ := hdvd
    refine Ideal.mem_span_singleton.mpr ⟨(c : ℤ_[ℓ]), ?_⟩
    have := congrArg (fun z : ℤ => (z : ℤ_[ℓ])) hc
    push_cast at this ⊢
    exact this

end Compensate

end CentralNebentypus

open NumberField NumberField.AdelicLevel AdelicDock AutomorphicForm IsDedekindDomain LocalNewvector CentralNebentypus in

theorem solution
    {M : ℕ} [NeZero M] {ε : DirichletCharacter ℂ M} {h : CuspForm (CongruenceSubgroup.Gamma1 M) 2}
    (hε : CuspForm.HasNebentypus ε h)
    (Φ : AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers ℚ) ℚ → ℂ)
    (hΦh : CuspForm.IsAdelicLiftOfGamma1 h Φ)
    (q : ℕ) [Fact q.Prime] (u : ℤ_[q]ˣ) (d : ℤ)
    (hdq : (d : ℤ_[q]) * u - 1 ∈ Ideal.span {(q : ℤ_[q]) ^ M.factorization q})
    (hdM : ((M / q ^ M.factorization q : ℕ) : ℤ) ∣ d - 1)
    (x : AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers ℚ) ℚ) :
    Φ (x * AdelicDock.padicToAdelic q
          (LocalNewvector.centralGL q (Units.map PadicInt.Coe.ringHom.toMonoidHom u))) =
      ε (d : ZMod M) * Φ x := by
  classical
  have hqp : q.Prime := Fact.out
  have hM0 : M ≠ 0 := NeZero.ne M
  set n : ℕ := M.factorization q with hn
  set M' : ℕ := M / q ^ n with hM'
  have hMfac : q ^ n * M' = M := Nat.ordProj_mul_ordCompl_eq_self M q

  have hcopM' : IsCoprime d (M' : ℤ) := by
    obtain ⟨c, hc⟩ := hdM
    refine ⟨1, -c, ?_⟩
    linear_combination hc
  have hcopq : IsCoprime d ((q : ℤ) ^ n) := by

    have hunit : IsUnit ((d : ZMod (q ^ n))) := by
      have h0 : PadicInt.toZModPow n ((d : ℤ_[q]) * (u : ℤ_[q]) - 1) = 0 := by
        rw [← RingHom.mem_ker, PadicInt.ker_toZModPow]
        exact hdq
      rw [map_sub, map_one, map_mul, map_intCast, sub_eq_zero] at h0
      exact IsUnit.of_mul_eq_one _ h0
    have := (ZMod.coe_int_isUnit_iff_isCoprime d (q ^ n)).mp hunit
    push_cast at this
    exact this.symm
  have hcop : IsCoprime d (M : ℤ) := by
    have hMZ : (M : ℤ) = (q : ℤ) ^ n * (M' : ℤ) := by exact_mod_cast hMfac.symm
    rw [hMZ]
    exact IsCoprime.mul_right hcopq hcopM'

  obtain ⟨σ, hσ, hσ11⟩ := exists_gamma0_lowerRight_eq (M := M) hcop
  have hk1 := glFin_globalPoints_mul_centralGL_mem_finiteLevelOne q hM0 hσ u
    (by rw [hσ11]; exact hdq) (by rw [hσ11]; exact hdM)
  set k : GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ) :=
    padicToFinAdelic q (centralGL q (Units.map PadicInt.Coe.ringHom.toMonoidHom u)) with hk
  have hkA : AdelicDock.padicToAdelic q (centralGL q (Units.map PadicInt.Coe.ringHom.toMonoidHom u))
      = finEmbed (𝓞 ℚ) ℚ k := rfl

  obtain ⟨γ, X, w, hXfin, hXpos, hw, hx⟩ := exists_eq_globalPoints_mul_mul_finEmbed_of_mem_finiteLevelOne hM0 x
  have hwk : finEmbed (𝓞 ℚ) ℚ w * finEmbed (𝓞 ℚ) ℚ k = finEmbed (𝓞 ℚ) ℚ k * finEmbed (𝓞 ℚ) ℚ w := by
    rw [← map_mul, ← map_mul, hk, padicToFinAdelic_centralGL_mul_comm]
  have hval : Φ (X * finEmbed (𝓞 ℚ) ℚ k) = ε ((σ 1 1 : ℤ) : ZMod M) * Φ X :=
    apply_mul_finEmbed_eq_of_mem_finiteLevelOne hε hΦh hσ hk1 hXfin hXpos
  have hR : Φ x = Φ X := by
    rw [hx, mul_assoc, hΦh.left_inv, hΦh.level_inv _ hw]
  have hL : Φ (x * finEmbed (𝓞 ℚ) ℚ k) = Φ (X * finEmbed (𝓞 ℚ) ℚ k) := by
    rw [hx, mul_assoc, mul_assoc, hwk, ← mul_assoc X, hΦh.left_inv, hΦh.level_inv _ hw]
  rw [hkA, hL, hR, hval, hσ11]

end

end S_CuspForm_HasNebentypus_apply_mul_padicToAdelic_centralGL_eq_of_isAdelicLiftOfGamma1
end P2MW
export P2MW.S_CuspForm_HasNebentypus_apply_mul_padicToAdelic_centralGL_eq_of_isAdelicLiftOfGamma1 (solution)
