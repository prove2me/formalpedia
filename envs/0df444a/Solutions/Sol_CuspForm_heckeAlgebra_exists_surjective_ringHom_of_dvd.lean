-- Prove2me | solution 1 for CuspForm.heckeAlgebra.exists_surjective_ringHom_of_dvd
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/9f3e4939-97af-5ec5-8bdc-5bb0e9886e2f

import Definitions.Def_CuspForm_HeckeAlgebra
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CuspForm_heckeAlgebra_exists_surjective_ringHom_of_dvd

set_option autoImplicit false

noncomputable section

open CongruenceSubgroup

namespace HresA

open scoped MatrixGroups ModularForm

variable {N N' : ℕ}

theorem gamma0_le_of_dvd (h : N ∣ N') : Gamma0 N' ≤ Gamma0 N := by
  intro γ hγ
  rw [Gamma0_mem] at hγ ⊢
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at hγ ⊢
  exact dvd_trans (Int.natCast_dvd_natCast.mpr h) hγ

theorem gamma0GL_le_of_dvd (h : N ∣ N') :
    ((Gamma0 N' : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) ≤
      ((Gamma0 N : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) :=
  Subgroup.map_mono (gamma0_le_of_dvd h)

variable (k : ℤ)

def levelIncl [NeZero N] [NeZero N'] (h : N ∣ N') :
    CuspForm (Gamma0 N) k →ₗ[ℂ] CuspForm (Gamma0 N') k where
  toFun f :=
    { toFun := ⇑f
      slash_action_eq' := fun γ hγ =>
        SlashInvariantFormClass.slash_action_eq f γ (gamma0GL_le_of_dvd h hγ)
      holo' := CuspFormClass.holo f
      zero_at_cusps' := fun {c} hc => by
        refine CuspFormClass.zero_at_cusps f ?_
        rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z] at hc ⊢
        exact hc }
  map_add' f g := rfl
  map_smul' c f := rfl

@[scoped simp] theorem coe_levelIncl [NeZero N] [NeZero N'] (h : N ∣ N') (f : CuspForm (Gamma0 N) k) :
    ⇑(levelIncl k h f) = ⇑f := rfl

theorem levelIncl_injective [NeZero N] [NeZero N'] (h : N ∣ N') :
    Function.Injective (levelIncl k h) := fun f g hfg =>
  DFunLike.coe_injective
    (by simpa using congrArg (fun x : CuspForm (Gamma0 N') k => ⇑x) hfg)

section Restrict

variable {k}
variable [NeZero N] [NeZero N'] (S : Set ℕ)

def Restricts (h : N ∣ N') (t : Module.End ℂ (CuspForm (Gamma0 N') k))
    (s : Module.End ℂ (CuspForm (Gamma0 N) k)) : Prop :=
  t ∘ₗ levelIncl k h = levelIncl k h ∘ₗ s

variable {S}
variable {h : N ∣ N'}

theorem Restricts.apply {t : Module.End ℂ (CuspForm (Gamma0 N') k)}
    {s : Module.End ℂ (CuspForm (Gamma0 N) k)} (hs : Restricts h t s)
    (f : CuspForm (Gamma0 N) k) : t (levelIncl k h f) = levelIncl k h (s f) :=
  LinearMap.congr_fun hs f

theorem Restricts.unique {t : Module.End ℂ (CuspForm (Gamma0 N') k)}
    {s s' : Module.End ℂ (CuspForm (Gamma0 N) k)} (hs : Restricts h t s)
    (hs' : Restricts h t s') : s = s' := by
  refine LinearMap.ext fun f => levelIncl_injective k h ?_
  rw [← hs.apply, ← hs'.apply]

theorem Restricts.one : Restricts h (1 : Module.End ℂ (CuspForm (Gamma0 N') k)) 1 := by
  refine LinearMap.ext fun f => ?_
  rfl

theorem Restricts.zero : Restricts h (0 : Module.End ℂ (CuspForm (Gamma0 N') k)) 0 := by
  refine LinearMap.ext fun f => ?_
  simp

theorem Restricts.add {t t' : Module.End ℂ (CuspForm (Gamma0 N') k)}
    {s s' : Module.End ℂ (CuspForm (Gamma0 N) k)} (hs : Restricts h t s)
    (hs' : Restricts h t' s') : Restricts h (t + t') (s + s') := by
  refine LinearMap.ext fun f => ?_
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.add_apply, map_add]
  rw [hs.apply, hs'.apply]

theorem Restricts.mul {t t' : Module.End ℂ (CuspForm (Gamma0 N') k)}
    {s s' : Module.End ℂ (CuspForm (Gamma0 N) k)} (hs : Restricts h t s)
    (hs' : Restricts h t' s') : Restricts h (t * t') (s * s') := by
  refine LinearMap.ext fun f => ?_
  simp only [LinearMap.coe_comp, Function.comp_apply, Module.End.mul_apply]
  rw [hs'.apply, hs.apply]

theorem Restricts.algebraMap (r : ℤ) :
    Restricts h (algebraMap ℤ (Module.End ℂ (CuspForm (Gamma0 N') k)) r)
      (algebraMap ℤ (Module.End ℂ (CuspForm (Gamma0 N) k)) r) := by
  refine LinearMap.ext fun f => ?_
  simp only [LinearMap.coe_comp, Function.comp_apply, Module.algebraMap_end_apply, map_zsmul]

theorem Restricts.heckeTLin {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓN' : ¬ ℓ ∣ N') (hℓN : ¬ ℓ ∣ N) :
    Restricts h (CuspForm.heckeTLin k hℓ hℓN') (CuspForm.heckeTLin k hℓ hℓN) := by
  refine LinearMap.ext fun f => DFunLike.coe_injective ?_
  rfl

variable (S h)

theorem exists_restricts (hN'S : ∀ q : ℕ, q.Prime → q ∣ N' → q ∈ S)
    (t : Module.End ℂ (CuspForm (Gamma0 N') k)) (ht : t ∈ CuspForm.heckeAlgebra N' k S) :
    ∃ s ∈ CuspForm.heckeAlgebra N k S, Restricts h t s := by
  refine Algebra.adjoin_induction (p := fun t _ => ∃ s ∈ CuspForm.heckeAlgebra N k S, Restricts h t s)
    ?_ ?_ ?_ ?_ ht
  · rintro t (⟨ℓ, hℓ, hℓN', hℓS, rfl⟩ | ⟨q, hqN', hq, hqS, rfl⟩)
    · exact ⟨_, CuspForm.heckeTLin_mem_heckeAlgebra hℓ (fun hd => hℓN' (hd.trans h)) hℓS,
        Restricts.heckeTLin hℓ hℓN' _⟩
    · exact absurd (hN'S q hq hqN') hqS
  · exact fun r => ⟨_, algebraMap_mem _ r, Restricts.algebraMap r⟩
  · rintro t t' - - ⟨s, hs, hts⟩ ⟨s', hs', hts'⟩
    exact ⟨s + s', add_mem hs hs', hts.add hts'⟩
  · rintro t t' - - ⟨s, hs, hts⟩ ⟨s', hs', hts'⟩
    exact ⟨s * s', mul_mem hs hs', hts.mul hts'⟩

variable {S h}

def res (hN'S : ∀ q : ℕ, q.Prime → q ∣ N' → q ∈ S) :
    CuspForm.heckeAlgebra N' k S →+* CuspForm.heckeAlgebra N k S where
  toFun t := ⟨(exists_restricts S h hN'S t.1 t.2).choose,
    (exists_restricts S h hN'S t.1 t.2).choose_spec.1⟩
  map_one' := Subtype.ext <|
    (exists_restricts S h hN'S _ (CuspForm.heckeAlgebra N' k S).one_mem).choose_spec.2.unique
      Restricts.one
  map_mul' t t' := Subtype.ext <|
    (exists_restricts S h hN'S _ (mul_mem t.2 t'.2)).choose_spec.2.unique
      ((exists_restricts S h hN'S t.1 t.2).choose_spec.2.mul
        (exists_restricts S h hN'S t'.1 t'.2).choose_spec.2)
  map_zero' := Subtype.ext <|
    (exists_restricts S h hN'S _ (CuspForm.heckeAlgebra N' k S).zero_mem).choose_spec.2.unique
      Restricts.zero
  map_add' t t' := Subtype.ext <|
    (exists_restricts S h hN'S _ (add_mem t.2 t'.2)).choose_spec.2.unique
      ((exists_restricts S h hN'S t.1 t.2).choose_spec.2.add
        (exists_restricts S h hN'S t'.1 t'.2).choose_spec.2)

theorem res_restricts (hN'S : ∀ q : ℕ, q.Prime → q ∣ N' → q ∈ S)
    (t : CuspForm.heckeAlgebra N' k S) :
    Restricts h (t : Module.End ℂ (CuspForm (Gamma0 N') k))
      ((res (h := h) hN'S t : CuspForm.heckeAlgebra N k S) :
        Module.End ℂ (CuspForm (Gamma0 N) k)) :=
  (exists_restricts S h hN'S t.1 t.2).choose_spec.2

theorem res_eq_of_restricts (hN'S : ∀ q : ℕ, q.Prime → q ∣ N' → q ∈ S)
    (t : CuspForm.heckeAlgebra N' k S) (s : CuspForm.heckeAlgebra N k S)
    (hs : Restricts h (t : Module.End ℂ (CuspForm (Gamma0 N') k))
      (s : Module.End ℂ (CuspForm (Gamma0 N) k))) :
    res (h := h) hN'S t = s :=
  Subtype.ext ((res_restricts hN'S t).unique hs)

theorem res_T (hN'S : ∀ q : ℕ, q.Prime → q ∣ N' → q ∈ S)
    {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓN' : ¬ ℓ ∣ N') (hℓN : ¬ ℓ ∣ N) (hℓS : ℓ ∉ S) :
    res (k := k) (h := h) hN'S (CuspForm.heckeAlgebra.T hℓ hℓN' hℓS) =
      (CuspForm.heckeAlgebra.T hℓ hℓN hℓS : CuspForm.heckeAlgebra N k S) :=
  res_eq_of_restricts hN'S _ _ (Restricts.heckeTLin hℓ hℓN' hℓN)

theorem coe_res_apply (hN'S : ∀ q : ℕ, q.Prime → q ∣ N' → q ∈ S)
    (t : CuspForm.heckeAlgebra N' k S) (f : CuspForm (Gamma0 N) k)
    (g : CuspForm (Gamma0 N') k) (hfg : ⇑g = ⇑f) :
    ⇑((res (h := h) hN'S t : Module.End ℂ (CuspForm (Gamma0 N) k)) f) =
      ⇑((t : Module.End ℂ (CuspForm (Gamma0 N') k)) g) := by
  have hg : g = levelIncl k h f := DFunLike.coe_injective (hfg.trans (coe_levelIncl k h f).symm)
  rw [hg, (res_restricts hN'S t).apply f]
  rfl

theorem res_surjective (hN'S : ∀ q : ℕ, q.Prime → q ∣ N' → q ∈ S) :
    Function.Surjective (res (k := k) (h := h) hN'S) := by
  rintro ⟨s, hs⟩
  refine Algebra.adjoin_induction (p := fun s hs => ∃ t, res (k := k) (h := h) hN'S t = ⟨s, hs⟩)
    ?_ ?_ ?_ ?_ hs
  · rintro s (⟨ℓ, hℓ, hℓN, hℓS, rfl⟩ | ⟨q, hqN, hq, hqS, rfl⟩)
    · have hℓN' : ¬ ℓ ∣ N' := fun hd => hℓS (hN'S ℓ hℓ hd)
      exact ⟨CuspForm.heckeAlgebra.T hℓ hℓN' hℓS, res_T hN'S hℓ hℓN' hℓN hℓS⟩
    · exact absurd (hN'S q hq (hqN.trans h)) hqS
  · exact fun r => ⟨algebraMap ℤ _ r, map_intCast _ r⟩
  · intro s s' _ _ H H'
    obtain ⟨t, hts⟩ := H
    obtain ⟨t', hts'⟩ := H'
    exact ⟨t + t', by rw [(res (k := k) (h := h) hN'S).map_add, hts, hts']; rfl⟩
  · intro s s' _ _ H H'
    obtain ⟨t, hts⟩ := H
    obtain ⟨t', hts'⟩ := H'
    exact ⟨t * t', by rw [(res (k := k) (h := h) hN'S).map_mul, hts, hts']; rfl⟩

end Restrict

end HresA
p2m_reactivate "P2MW.S_CuspForm_heckeAlgebra_exists_surjective_ringHom_of_dvd.HresA"

end
p2m_reactivate "P2MW.S_CuspForm_heckeAlgebra_exists_surjective_ringHom_of_dvd.HresA"

open HresA in
theorem solution
    (N N' : ℕ) [NeZero N] [NeZero N'] (hNN' : N ∣ N') (k : ℤ) (S : Set ℕ)
    (hN'S : ∀ q : ℕ, q.Prime → q ∣ N' → q ∈ S) :
    ∃ res : CuspForm.heckeAlgebra N' k S →+* CuspForm.heckeAlgebra N k S,
      Function.Surjective res ∧
      (∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN' : ¬ ℓ ∣ N') (hℓN : ¬ ℓ ∣ N) (hℓS : ℓ ∉ S),
        res (CuspForm.heckeAlgebra.T hℓ hℓN' hℓS) = CuspForm.heckeAlgebra.T hℓ hℓN hℓS) ∧
      ∀ (t : CuspForm.heckeAlgebra N' k S) (f : CuspForm (CongruenceSubgroup.Gamma0 N) k)
        (g : CuspForm (CongruenceSubgroup.Gamma0 N') k), ⇑g = ⇑f →
        ⇑((res t : Module.End ℂ (CuspForm (CongruenceSubgroup.Gamma0 N) k)) f) =
          ⇑((t : Module.End ℂ (CuspForm (CongruenceSubgroup.Gamma0 N') k)) g) :=
  ⟨HresA.res (k := k) (h := hNN') hN'S, HresA.res_surjective hN'S,
    fun _ hℓ hℓN' hℓN hℓS => HresA.res_T hN'S hℓ hℓN' hℓN hℓS,
    fun t f g hfg => HresA.coe_res_apply hN'S t f g hfg⟩

end S_CuspForm_heckeAlgebra_exists_surjective_ringHom_of_dvd
end P2MW
export P2MW.S_CuspForm_heckeAlgebra_exists_surjective_ringHom_of_dvd (solution)
