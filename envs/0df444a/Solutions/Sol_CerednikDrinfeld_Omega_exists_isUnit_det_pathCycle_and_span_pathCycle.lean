-- Prove2me | solution 1 for CerednikDrinfeld.Omega.exists_isUnit_det_pathCycle_and_span_pathCycle
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/5e5af87f-01b3-5c4d-bd95-e7f197867a83

import Mathlib
import Definitions.Def_CerednikDrinfeld_ThetaMer
import Definitions.Def_CerednikDrinfeld_DiscreteProjectiveAction
import Definitions.Def_CerednikDrinfeld_MumfordQuotient
import Definitions.Def_CerednikDrinfeld_SchottkyTreeAction
import Definitions.Def_CerednikDrinfeld_BruhatTitsTree
import Theorems.Thm_exists_spanningTree_of_connected
import Theorems.Thm_exists_fundamentalCycles_of_spanningTree
import Theorems.Thm_CerednikDrinfeld_Mumford_exists_addMonoidHom_abelianization_ribbonKernel_apply_eq_pathCycle
import Theorems.Thm_CerednikDrinfeld_Mumford_surjective_and_apply_eq_zero_iff_mem_closure_stabilizer_of_apply_eq_pathCycle
import Theorems.Thm_CerednikDrinfeld_BruhatTits_tree_isTree
import Theorems.Thm_CerednikDrinfeld_BruhatTits_tree_connected_and_colorable_two
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_Omega_exists_isUnit_det_pathCycle_and_span_pathCycle

set_option autoImplicit false

open scoped MatrixGroups
open CerednikDrinfeld.Omega CerednikDrinfeld.Mumford

set_option autoImplicit false

open scoped MatrixGroups
open CerednikDrinfeld.Omega CerednikDrinfeld.Mumford

namespace CycleBasisAux

open MulAction

variable {G : Type} [Group G] {W : Type} [MulAction G W] {𝒯 : SimpleGraph W} [GraphAction G 𝒯]

theorem tau_eq_of_mk_eq (τ : W → ZMod 2) (hτ : ∀ (g : G) (w : W), τ (g • w) = τ w) {x y : W}
    (h : (Quotient.mk (orbitRel G W) x : QuotVert G W) = Quotient.mk (orbitRel G W) y) : τ x = τ y := by
  obtain ⟨g, rfl⟩ := mem_orbit_iff.1 (orbitRel_apply.1 (Quotient.eq.1 h))
  exact hτ g y

theorem mk_out_fst (d : 𝒯.Dart) :
    (Quotient.mk (orbitRel G W) (Quotient.mk (orbitRel G 𝒯.Dart) d : QuotEdge G 𝒯).out.fst : QuotVert G W) =
      Quotient.mk (orbitRel G W) d.fst := by
  obtain ⟨g, hg⟩ := mem_orbit_iff.1 (orbitRel_apply.1 (Quotient.mk_out (s := orbitRel G 𝒯.Dart) d))
  rw [← hg, smul_dart_fst]
  exact Quotient.sound (orbitRel_apply.2 (mem_orbit d.fst g))

theorem mk_out_snd (d : 𝒯.Dart) :
    (Quotient.mk (orbitRel G W) (Quotient.mk (orbitRel G 𝒯.Dart) d : QuotEdge G 𝒯).out.snd : QuotVert G W) =
      Quotient.mk (orbitRel G W) d.snd := by
  obtain ⟨g, hg⟩ := mem_orbit_iff.1 (orbitRel_apply.1 (Quotient.mk_out (s := orbitRel G 𝒯.Dart) d))
  rw [← hg, smul_dart_snd]
  exact Quotient.sound (orbitRel_apply.2 (mem_orbit d.snd g))

theorem tau_out_fst_mk (τ : W → ZMod 2) (hτ : ∀ (g : G) (w : W), τ (g • w) = τ w) (d : 𝒯.Dart) :
    τ (Quotient.mk (orbitRel G 𝒯.Dart) d : QuotEdge G 𝒯).out.fst = τ d.fst :=
  tau_eq_of_mk_eq τ hτ (mk_out_fst d)

theorem zmod_two_eq_zero_of_ne {a b : ZMod 2} (hab : a ≠ b) (hb : b ≠ 0) : a = 0 := by
  revert a b hab hb; decide

theorem pushforward_apply {E V : Type} [Fintype E] [DecidableEq V] (f : E → V) (x : E → ℤ) (v : V) :
    CerednikDrinfeld.pushforward f x v = ∑ e with f e = v, x e := by
  rw [Finset.sum_filter]
  simp only [CerednikDrinfeld.pushforward, Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct,
    CerednikDrinfeld.degeneracyMatrix, Matrix.of_apply, ite_mul, one_mul, zero_mul]

theorem mem_ribbonKernel_iff {E V : Type} [Fintype E] [DecidableEq V] (D : CerednikDrinfeld.DegeneracyData E V)
    (x : E → ℤ) :
    x ∈ CerednikDrinfeld.ribbonKernel D ↔
      (∀ v, ∑ e with D.a e = v, x e = 0) ∧ (∀ v, ∑ e with D.b e = v, x e = 0) := by
  rw [CerednikDrinfeld.mem_ribbonKernel, Fin.forall_fin_two]
  simp only [CerednikDrinfeld.jointDelta, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
  constructor
  · rintro ⟨ha, hb⟩
    exact ⟨fun v => by rw [← pushforward_apply]; exact congrFun ha v,
      fun v => by rw [← pushforward_apply]; exact congrFun hb v⟩
  · rintro ⟨ha, hb⟩
    exact ⟨funext fun v => by rw [pushforward_apply]; exact ha v, funext fun v => by rw [pushforward_apply]; exact hb v⟩

end CycleBasisAux

theorem solution
    (R K₀ : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K₀] [Algebra R K₀]
    [IsFractionRing R K₀] (ϖ : R) (hϖ : Irreducible ϖ) [Finite (R ⧸ Ideal.span {ϖ})]
    (K : Type) [Field K] [Algebra K₀ K] [DecidableEq K]
    {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀] [CompleteSpace K] [IsAlgClosed K]
    (hint : ∀ a : R, Valued.v (algebraMap K₀ K (algebraMap R K₀ a)) ≤ 1)
    (hv : ∀ a : K₀, Valued.v (algebraMap K₀ K a) ≤ 1 → IsLocalization.IsInteger R a)
    (hq : ∀ ε : Γ₀, ε ≠ 0 → ∃ N : ℕ, Valued.v (algebraMap K₀ K (algebraMap R K₀ ϖ)) ^ N ≤ ε)
    (hrk : ∀ x y : K, Valued.v x < 1 → y ≠ 0 → ∃ n : ℕ, Valued.v x ^ n ≤ Valued.v y)
    (ϖ₁ : PseudoUniformizer K₀ K) (hex : IsExhausted ϖ₁) [IsDomain ↥(holRing ϖ₁)]
    {G : Type} [Group G] (ρ : G →* PGL(2, K₀))
    [MulAction G (LT.LatticeTree.Vertex R K₀)]
    [CerednikDrinfeld.Mumford.GraphAction G (CerednikDrinfeld.BruhatTits.tree R K₀)]
    (hρ : CerednikDrinfeld.Mumford.ActsThrough (LT.LatticeTree.Vertex R K₀) ρ)

    (hfin : ∀ w : LT.LatticeTree.Vertex R K₀, Finite (MulAction.stabilizer G w))
    [Finite (CerednikDrinfeld.Mumford.QuotVert G (LT.LatticeTree.Vertex R K₀))]
    (τ : LT.LatticeTree.Vertex R K₀ → ZMod 2) (hτ : ∀ (g : G) (w : LT.LatticeTree.Vertex R K₀), τ (g • w) = τ w)
    (hadj : ∀ u w : LT.LatticeTree.Vertex R K₀, (CerednikDrinfeld.BruhatTits.tree R K₀).Adj u w → τ u ≠ τ w)
    (htame : ∀ w : LT.LatticeTree.Vertex R K₀, Valued.v ((Nat.card ↥(MulAction.stabilizer G w) : ℕ) : K) = 1)
    [DecidableEq (CerednikDrinfeld.Mumford.QuotEdge G (CerednikDrinfeld.BruhatTits.tree R K₀))]
    {E : Type} [Fintype E]
    (eE : E ≃ {e : CerednikDrinfeld.Mumford.QuotEdge G (CerednikDrinfeld.BruhatTits.tree R K₀) // τ e.out.fst = 0}) :
    ∃ (r : ℕ) (β : Fin r → G) (ι : Fin r → E),
      Function.Injective ι ∧
      IsUnit (Matrix.of (fun i j : Fin r =>
        CerednikDrinfeld.Mumford.pathCycle (CerednikDrinfeld.BruhatTits.tree R K₀) (fun e' => (eE e').1)
          (LT.LatticeTree.stdVertex R K₀) (β j) (ι i))).det ∧
      ∀ γ : G, ∃ n : Fin r → ℤ, ∀ e : E,
        CerednikDrinfeld.Mumford.pathCycle (CerednikDrinfeld.BruhatTits.tree R K₀) (fun e' => (eE e').1)
            (LT.LatticeTree.stdVertex R K₀) γ e
          = ∑ j, n j * CerednikDrinfeld.Mumford.pathCycle (CerednikDrinfeld.BruhatTits.tree R K₀) (fun e' => (eE e').1)
            (LT.LatticeTree.stdVertex R K₀) (β j) e := by
  classical

  haveI : Fintype (QuotVert G (LT.LatticeTree.Vertex R K₀)) := Fintype.ofFinite _
  have hT : (CerednikDrinfeld.BruhatTits.tree R K₀).IsTree := CerednikDrinfeld.BruhatTits.tree_isTree R K₀
  have hconnT := (CerednikDrinfeld.BruhatTits.tree_connected_and_colorable_two R K₀).1

  let hd : E → QuotVert G (LT.LatticeTree.Vertex R K₀) := fun e =>
    Quotient.mk (MulAction.orbitRel G (LT.LatticeTree.Vertex R K₀)) (eE e).1.out.fst
  let tl : E → QuotVert G (LT.LatticeTree.Vertex R K₀) := fun e =>
    Quotient.mk (MulAction.orbitRel G (LT.LatticeTree.Vertex R K₀)) (eE e).1.out.snd
  let D : CerednikDrinfeld.DegeneracyData E (QuotVert G (LT.LatticeTree.Vertex R K₀)) := ⟨hd, tl, fun _ => 1⟩

  have hcol0 : ∀ e : E, τ (eE e).1.out.fst = 0 := fun e => (eE e).2
  have hcol1 : ∀ e : E, τ (eE e).1.out.snd ≠ 0 := fun e h =>
    hadj _ _ (eE e).1.out.adj ((hcol0 e).trans h.symm)
  have hsep : ∀ e e' : E, hd e ≠ tl e' := fun e e' h =>
    hcol1 e' ((CycleBasisAux.tau_eq_of_mk_eq τ hτ h).symm.trans (hcol0 e))

  have kir_of_mem : ∀ x : E → ℤ, x ∈ CerednikDrinfeld.ribbonKernel D →
      ∀ w, (∑ e with hd e = w, x e) = (∑ e with tl e = w, x e) := by
    intro x hx w
    obtain ⟨ha, hb⟩ := (CycleBasisAux.mem_ribbonKernel_iff D x).1 hx
    rw [ha w, hb w]
  have mem_of_kir : ∀ x : E → ℤ, (∀ w, (∑ e with hd e = w, x e) = (∑ e with tl e = w, x e)) →
      x ∈ CerednikDrinfeld.ribbonKernel D := by
    intro x hx
    rw [CycleBasisAux.mem_ribbonKernel_iff]
    refine ⟨fun w => ?_, fun w => ?_⟩
    · by_cases h : ∃ e, hd e = w
      · obtain ⟨e₀, he₀⟩ := h
        rw [hx w]
        refine Finset.sum_eq_zero fun e he => ?_
        rw [Finset.mem_filter] at he
        exact absurd (he₀.trans he.2.symm) (hsep e₀ e)
      · push Not at h
        refine Finset.sum_eq_zero fun e he => ?_
        rw [Finset.mem_filter] at he
        exact absurd he.2 (h e)
    · by_cases h : ∃ e, tl e = w
      · obtain ⟨e₀, he₀⟩ := h
        rw [← hx w]
        refine Finset.sum_eq_zero fun e he => ?_
        rw [Finset.mem_filter] at he
        exact absurd (he.2.trans he₀.symm) (hsep e e₀)
      · push Not at h
        refine Finset.sum_eq_zero fun e he => ?_
        rw [Finset.mem_filter] at he
        exact absurd he.2 (h e)

  obtain ⟨Φ, hΦ⟩ := CerednikDrinfeld.Mumford.exists_addMonoidHom_abelianization_ribbonKernel_apply_eq_pathCycle
    (CerednikDrinfeld.BruhatTits.tree R K₀) hT τ hτ hadj D eE (Equiv.refl _) (fun _ => rfl) (fun _ => rfl)
    (LT.LatticeTree.stdVertex R K₀)
  obtain ⟨hsurj, -⟩ :=
    CerednikDrinfeld.Mumford.surjective_and_apply_eq_zero_iff_mem_closure_stabilizer_of_apply_eq_pathCycle
      (CerednikDrinfeld.BruhatTits.tree R K₀) hT τ hτ hadj D eE (Equiv.refl _) (fun _ => rfl) (fun _ => rfl)
      (LT.LatticeTree.stdVertex R K₀) Φ hΦ

  have hdart : ∀ (d : (CerednikDrinfeld.BruhatTits.tree R K₀).Dart) (w : QuotVert G (LT.LatticeTree.Vertex R K₀)),
      (∑ e with hd e = w, CerednikDrinfeld.Mumford.dartIndex (CerednikDrinfeld.BruhatTits.tree R K₀) (eE e).1 d) -
        (∑ e with tl e = w, CerednikDrinfeld.Mumford.dartIndex (CerednikDrinfeld.BruhatTits.tree R K₀) (eE e).1 d) =
      (if Quotient.mk (MulAction.orbitRel G _) d.fst = w then 1 else 0) -
        (if Quotient.mk (MulAction.orbitRel G _) d.snd = w then 1 else 0) := by
    intro d w
    have hne : τ d.fst ≠ τ d.snd := hadj _ _ d.adj
    by_cases h0 : τ d.fst = 0
    ·
      let e₀ : E := eE.symm ⟨Quotient.mk _ d, by rw [CycleBasisAux.tau_out_fst_mk τ hτ]; exact h0⟩
      have he₀ : (eE e₀).1 = Quotient.mk _ d := by simp [e₀]
      have hidx : ∀ e : E, CerednikDrinfeld.Mumford.dartIndex (CerednikDrinfeld.BruhatTits.tree R K₀) (eE e).1 d =
          if e = e₀ then 1 else 0 := by
        intro e
        rw [CerednikDrinfeld.Mumford.dartIndex]
        have h2 : ¬ Quotient.mk (MulAction.orbitRel G _) d.symm = (eE e).1 := by
          intro h
          have := CycleBasisAux.tau_out_fst_mk (𝒯 := CerednikDrinfeld.BruhatTits.tree R K₀) τ hτ d.symm
          rw [h, hcol0 e] at this
          exact hne (h0.trans (this.trans (by rfl)))
        rw [if_neg h2, sub_zero]
        by_cases he : e = e₀
        · rw [if_pos he, if_pos (by rw [he, he₀])]
        · rw [if_neg he, if_neg]
          intro h
          exact he (eE.injective (Subtype.ext (h.symm.trans he₀.symm)))
      simp_rw [hidx]
      simp only [Finset.sum_ite_eq', Finset.mem_filter, Finset.mem_univ, true_and]
      have h1 : hd e₀ = Quotient.mk _ d.fst := by
        show Quotient.mk _ (eE e₀).1.out.fst = _; rw [he₀]; exact CycleBasisAux.mk_out_fst d
      have h2 : tl e₀ = Quotient.mk _ d.snd := by
        show Quotient.mk _ (eE e₀).1.out.snd = _; rw [he₀]; exact CycleBasisAux.mk_out_snd d
      rw [h1, h2]
    ·
      have h1c : τ d.snd = 0 := CycleBasisAux.zmod_two_eq_zero_of_ne hne.symm h0
      let e₁ : E := eE.symm ⟨Quotient.mk _ d.symm, by rw [CycleBasisAux.tau_out_fst_mk τ hτ]; exact h1c⟩
      have he₁ : (eE e₁).1 = Quotient.mk _ d.symm := by simp [e₁]
      have hidx : ∀ e : E, CerednikDrinfeld.Mumford.dartIndex (CerednikDrinfeld.BruhatTits.tree R K₀) (eE e).1 d =
          if e = e₁ then -1 else 0 := by
        intro e
        rw [CerednikDrinfeld.Mumford.dartIndex]
        have h2 : ¬ Quotient.mk (MulAction.orbitRel G _) d = (eE e).1 := by
          intro h
          have := CycleBasisAux.tau_out_fst_mk (𝒯 := CerednikDrinfeld.BruhatTits.tree R K₀) τ hτ d
          rw [h, hcol0 e] at this
          exact h0 this.symm
        rw [if_neg h2, zero_sub]
        by_cases he : e = e₁
        · rw [if_pos he, if_pos (by rw [he, he₁])]
        · rw [if_neg he, if_neg, neg_zero]
          intro h
          exact he (eE.injective (Subtype.ext (h.symm.trans he₁.symm)))
      simp_rw [hidx]
      simp only [Finset.sum_ite_eq', Finset.mem_filter, Finset.mem_univ, true_and]
      have h1 : hd e₁ = Quotient.mk _ d.snd := by
        show Quotient.mk _ (eE e₁).1.out.fst = _; rw [he₁]; exact CycleBasisAux.mk_out_fst d.symm
      have h2 : tl e₁ = Quotient.mk _ d.fst := by
        show Quotient.mk _ (eE e₁).1.out.snd = _; rw [he₁]; exact CycleBasisAux.mk_out_snd d.symm
      rw [h1, h2]
      split_ifs <;> ring
  have hwalk : ∀ {x y : LT.LatticeTree.Vertex R K₀} (p : (CerednikDrinfeld.BruhatTits.tree R K₀).Walk x y)
      (w : QuotVert G (LT.LatticeTree.Vertex R K₀)),
      (∑ e with hd e = w, CerednikDrinfeld.Mumford.walkCycle (CerednikDrinfeld.BruhatTits.tree R K₀) (fun e' => (eE e').1) p e) -
        (∑ e with tl e = w, CerednikDrinfeld.Mumford.walkCycle (CerednikDrinfeld.BruhatTits.tree R K₀) (fun e' => (eE e').1) p e) =
      (if Quotient.mk (MulAction.orbitRel G _) x = w then 1 else 0) -
        (if Quotient.mk (MulAction.orbitRel G _) y = w then 1 else 0) := by
    intro x y p w
    induction p with
    | nil => simp
    | cons h p ih =>
      simp_rw [CerednikDrinfeld.Mumford.walkCycle_cons]
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib, add_sub_add_comm, ih, hdart]
      dsimp only
      ring

  have hconn : ∀ u v : QuotVert G (LT.LatticeTree.Vertex R K₀), ∃ c : E → ℤ,
      ∀ w, (∑ e with hd e = w, c e) - (∑ e with tl e = w, c e) =
        (if w = v then 1 else 0) - (if w = u then 1 else 0) := by
    intro u v
    obtain ⟨p⟩ := hconnT.preconnected v.out u.out
    refine ⟨CerednikDrinfeld.Mumford.walkCycle (CerednikDrinfeld.BruhatTits.tree R K₀) (fun e' => (eE e').1) p, fun w => ?_⟩
    rw [hwalk p w, Quotient.out_eq, Quotient.out_eq]
    simp only [eq_comm (a := w)]

  obtain ⟨T, hTsp⟩ := exists_spanningTree_of_connected hd tl hconn
  obtain ⟨Z, hZcyc, hZid, -, hZgen⟩ := exists_fundamentalCycles_of_spanningTree hd tl T hTsp

  obtain ⟨r, ιe⟩ : ∃ r : ℕ, Nonempty (↥(Tᶜ) ≃ Fin r) := ⟨_, ⟨Fintype.equivFin _⟩⟩
  obtain ⟨ιe⟩ := ιe
  let ι : Fin r → E := fun i => ((ιe.symm i : ↥(Tᶜ)) : E)
  have hιmem : ∀ i, ι i ∈ Tᶜ := fun i => (ιe.symm i).2
  have hιinj : Function.Injective ι := fun i j h => ιe.symm.injective (Subtype.ext h)
  have hZmem : ∀ i, Z (ι i) ∈ CerednikDrinfeld.ribbonKernel D := fun i => mem_of_kir _ (hZcyc (ι i))
  have hlift : ∀ i, ∃ g : G, CerednikDrinfeld.Mumford.pathCycle (CerednikDrinfeld.BruhatTits.tree R K₀) (fun e' => (eE e').1)
      (LT.LatticeTree.stdVertex R K₀) g = Z (ι i) := by
    intro i
    obtain ⟨x, hx⟩ := hsurj ⟨Z (ι i), hZmem i⟩
    obtain ⟨g, hg⟩ := QuotientGroup.mk_surjective (Additive.toMul x)
    refine ⟨g, ?_⟩
    rw [← hΦ g]
    have : Additive.ofMul (Abelianization.of g) = x := by
      rw [show Abelianization.of g = QuotientGroup.mk g from rfl, hg]; rfl
    rw [this, hx]
  choose β hβ using hlift
  refine ⟨r, β, ι, hιinj, ?_, fun γ => ?_⟩
  ·
    have hM : Matrix.of (fun i j : Fin r =>
        CerednikDrinfeld.Mumford.pathCycle (CerednikDrinfeld.BruhatTits.tree R K₀) (fun e' => (eE e').1)
          (LT.LatticeTree.stdVertex R K₀) (β j) (ι i)) = 1 := by
      ext i j
      rw [Matrix.of_apply, hβ j, hZid (ι j) (hιmem j) (ι i) (hιmem i), Matrix.one_apply]
      by_cases hij : i = j
      · rw [if_pos (by rw [hij]), if_pos hij]
      · rw [if_neg (fun h => hij (hιinj h).symm), if_neg hij]
    rw [hM, Matrix.det_one]
    exact isUnit_one
  ·
    have hkir := kir_of_mem (CerednikDrinfeld.Mumford.pathCycle (CerednikDrinfeld.BruhatTits.tree R K₀) (fun e' => (eE e').1)
      (LT.LatticeTree.stdVertex R K₀) γ) (by rw [← hΦ γ]; exact (Φ _).2)
    refine ⟨fun j => CerednikDrinfeld.Mumford.pathCycle (CerednikDrinfeld.BruhatTits.tree R K₀) (fun e' => (eE e').1)
      (LT.LatticeTree.stdVertex R K₀) γ (ι j), fun e => ?_⟩
    rw [hZgen _ hkir e]
    simp_rw [hβ]
    rw [← Finset.sum_coe_sort (Tᶜ)]
    rw [← Equiv.sum_comp ιe.symm]
    refine Fintype.sum_congr _ _ fun i => ?_
    simp only [Function.comp_apply, smul_eq_mul, ι]
    ring

end S_CerednikDrinfeld_Omega_exists_isUnit_det_pathCycle_and_span_pathCycle
end P2MW
export P2MW.S_CerednikDrinfeld_Omega_exists_isUnit_det_pathCycle_and_span_pathCycle (solution)
