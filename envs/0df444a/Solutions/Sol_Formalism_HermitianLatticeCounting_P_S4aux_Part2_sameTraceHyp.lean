-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.S4aux.Part2.sameTraceHyp
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:58:58.843537+00:00
-- url     : https://prove2.me/submissions/8468b97d-5caa-4e14-915b-a767577e1422

import Definitions.Def_Formalism_FlagUnipotentLattices_PairingOrthogonalComplement
import Definitions.Def_Formalism_SobolevGaussianKernels_KernelBoundRel
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_SuperdiagonalAdditionInvariance
import Theorems.Thm_Formalism_SL_P_SphereChartDerivatives_sn_cast
import Theorems.Thm_Formalism_SL_P_SphereChartDerivatives_sn_last
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.SL.P.SphereChartDerivatives.sn_cast
attribute [local simp] Formalism.SL.P.SphereChartDerivatives.sn_last



set_option autoImplicit false
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P Formalism.HermitianLatticeCounting.P.S4aux
open Formalism.HermitianLatticeCounting.S4 Formalism.SL.IwahoriBlocks Finset
open Formalism.HermitianLatticeCounting.P.S4aux.Part2
namespace Formalism.HermitianLatticeCounting.P.S4aux.Part2
theorem _root_.solution (H : DualCap) (HV : DualCapV) : SameTraceHyp := by
  intro o O' Lam' _ _ _ _ _ _ _ _ _ _ h' E _ _ V _ _ h O abelian₂ io j hU hSD hM hh hunit hspan r e he heL hli hprim

  have nd' : ∀ w' : Lam', (∀ v', h' v' w' = 0) → w' = 0 := by
    intro w' hw'
    let bs := Module.Free.chooseBasis O' Lam'
    apply bs.ext_elem
    intro i
    obtain ⟨W, hW⟩ := hSD.2 (bs.coord i)
    have h1 : bs.coord i w' = h' w' W := hW w'
    have h2 : h' w' W = 0 := by rw [hSD.1 W w', hw' W, star_zero]
    have h3 : bs.repr w' i = 0 := by rw [← Module.Basis.coord_apply, h1, h2]
    rw [h3]; simp
  have nd : ∀ v, (∀ w, h w v = 0) → v = 0 := by
    intro v hv
    obtain ⟨c, hc, hcv⟩ := hspan v
    obtain ⟨v', hv'⟩ := (hM.j_range _).mp hcv
    have : v' = 0 := nd' v' fun x' => hM.io_inj (by
      rw [← hM.form, hv', map_zero]; simp [hv])
    rw [this, map_zero] at hv'
    obtain ⟨u, hu⟩ := hunit c hc
    have : v = ((u⁻¹ : Eˣ) : E) • (io (algebraMap o O' c) • v) := by rw [← hu, smul_smul]; simp
    rw [this, ← hv', smul_zero]
  have uniq : ∀ c c' : Fin r → E, (∑ i, c i • e i) = (∑ i, c' i • e i) → ∀ i, c i = c' i := by
    intro c c' hcc i
    have h0 : ∑ i, (c i - c' i) • e i = 0 := by
      simp only [sub_smul, Finset.sum_sub_distrib, hcc, sub_self]
    exact sub_eq_zero.mp (Fintype.linearIndependent_iff.mp hli _ h0 i)

  have part1 : ∃ y : Fin r → V, (∀ k, y k ∈ abelian₂) ∧ ∀ i k, h (y k) (e i) = if i = k then 1 else 0 := by
    let Z₁ : Submodule E V := Submodule.span E (Set.range e)
    let S' : Submodule O' Lam' :=
      { carrier := {v | j v ∈ Z₁}
        add_mem' := fun {a b} ha hb => by
          show j (a + b) ∈ Z₁
          rw [map_add]; exact Z₁.add_mem ha hb
        zero_mem' := by
          show j 0 ∈ Z₁
          rw [map_zero]; exact Z₁.zero_mem
        smul_mem' := fun a v hv => by
          show j (a • v) ∈ Z₁
          rw [hM.j_smul]; exact Z₁.smul_mem _ hv }
    have hsat : Satur o S' := by
      intro c v hc hmem
      have h1 : io (algebraMap o O' c) • j v ∈ Z₁ := by rw [← hM.j_smul]; exact hmem
      obtain ⟨u, hu⟩ := hunit c hc
      have h2 : j v = ((u⁻¹ : Eˣ) : E) • (io (algebraMap o O' c) • j v) := by
        rw [← hu, smul_smul]; simp
      show j v ∈ Z₁
      rw [h2]; exact Z₁.smul_mem _ h1
    have hex : ∀ v : S', ∃ a : Fin r → O', j v = ∑ i, io (a i) • e i := by
      intro v
      obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun E).mp v.2
      have hcO := hprim c (by rw [hc]; exact (hM.j_range _).mpr ⟨v, rfl⟩)
      choose a ha using fun i => (hM.io_range _).mp (hcO i)
      exact ⟨a, by rw [← hc]; exact Finset.sum_congr rfl fun i _ => by rw [ha]⟩
    choose A hA using hex
    have Auniq : ∀ (v : S') (a : Fin r → O'), j v = ∑ i, io (a i) • e i → ∀ i, A v i = a i := by
      intro v a hva i
      exact hM.io_inj (uniq _ _ ((hA v).symm.trans hva) i)
    let φ : Fin r → S' →ₗ[O'] O' := fun k =>
      { toFun := fun v => A v k
        map_add' := fun a b => Auniq (a + b) (fun i => A a i + A b i) (by
          show j (a.1 + b.1) = _
          rw [map_add, hA a, hA b, ← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl fun i _ => by rw [map_add, add_smul]) k
        map_smul' := fun c a => Auniq (c • a) (fun i => c * A a i) (by
          show j (c • a.1) = _
          rw [hM.j_smul, hA a, Finset.smul_sum]
          exact Finset.sum_congr rfl fun i _ => by rw [map_mul, mul_smul]) k }
    choose w hw using fun k => H o O' Lam' h' hU hSD S' hsat (φ k)
    choose e' he' using fun i => (hM.j_range _).mp (heL i)
    have he'S : ∀ i, e' i ∈ S' := fun i => by
      show j (e' i) ∈ Z₁
      rw [he']; exact Submodule.subset_span ⟨i, rfl⟩
    refine ⟨fun k => j (w k), fun k => (hM.j_range _).mpr ⟨_, rfl⟩, fun i k => ?_⟩
    have h1 : A ⟨e' i, he'S i⟩ k = if i = k then 1 else 0 :=
      Auniq ⟨e' i, he'S i⟩ (fun l => if i = l then 1 else 0) (by
        show j (e' i) = _
        rw [he']; simp [apply_ite io]) k
    have h2 : h' (e' i) (w k) = if i = k then 1 else 0 := by
      rw [← h1]; exact (hw k ⟨e' i, he'S i⟩).symm
    have h3 : h (e i) (j (w k)) = if i = k then 1 else 0 := by
      rw [← he', hM.form, h2]; split_ifs <;> simp
    rw [hh (e i) (j (w k)), h3]; split_ifs <;> simp
  refine ⟨part1, ?_⟩
  obtain ⟨y, hyL, hye⟩ := part1
  intro d hd hdO
  let Z : Submodule E V :=
    { carrier := {v | ∀ i, h v (e i) = 0}
      add_mem' := fun {a b} ha hb i => by
        show h (a + b) (e i) = 0
        rw [map_add, LinearMap.add_apply, ha i, hb i, add_zero]
      zero_mem' := fun i => by
        show h 0 (e i) = 0
        simp
      smul_mem' := fun c v hv i => by
        show h (c • v) (e i) = 0
        rw [map_smul, LinearMap.smul_apply, hv i, smul_zero] }
  obtain ⟨l, hl, hlZ⟩ := HV o O' Lam' h' E V h O abelian₂ io j hU hSD hM hunit hspan Z d (fun w hw hwZ => hdO w hw hwZ)
  set v := d - l with hv
  set c : Fin r → E := fun i => star (h (y i) v) with hc
  have hzero : v - ∑ i, c i • e i = 0 := by
    apply nd
    intro w
    set w₀ := w - ∑ k, h w (e k) • y k with hw₀
    have hw₀Z : w₀ ∈ Z := by
      intro i
      show h w₀ (e i) = 0
      rw [hw₀, map_sub, LinearMap.sub_apply, map_sum, LinearMap.sum_apply]
      simp [hye]
    have e1 : w = w₀ + ∑ k, h w (e k) • y k := by rw [hw₀]; abel
    have a1 : h w₀ (v - ∑ i, c i • e i) = 0 := by
      rw [map_sub, hlZ w₀ hw₀Z, map_sum]
      have hz : ∀ i, h w₀ (e i) = 0 := hw₀Z
      simp [hz]
    have a2 : ∀ k, h (y k) (v - ∑ i, c i • e i) = 0 := by
      intro k
      rw [map_sub, map_sum]
      simp [hye, hc, starRingEnd_apply]
    rw [e1, map_add, LinearMap.add_apply, a1, map_sum, LinearMap.sum_apply]
    simp [a2]
  have hdl : d = l + ∑ i, c i • e i := by
    have : v = ∑ i, c i • e i := sub_eq_zero.mp hzero
    rw [← this, hv]; abel
  refine ⟨l, hl, fun i => ?_, c, hdl⟩
  have : l = d - ∑ k, c k • e k := by rw [hdl]; abel
  rw [this, map_sub, LinearMap.sub_apply, hd i, map_sum, LinearMap.sum_apply]
  simp [he]
end Formalism.HermitianLatticeCounting.P.S4aux.Part2
