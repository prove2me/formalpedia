-- Prove2me | solution 1 for FasterDistributedMatching.ApproximateMatching.power_color_lift
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-17T15:53:25.393713+00:00
-- url     : https://prove2.me/submissions/2c514662-ff56-4097-b9d9-b6dfb41d641d

import Definitions.Def_FasterDistributedMatching_ApproximateMatching_Routing

open Classical Finset
open FasterDistributedMatching.ApproximateMatching

noncomputable section
namespace CopyColorProof

variable {N : ℕ} (G : SimpleGraph (Fin N))

lemma line_walk_of_walk {u v : Fin N} (w : G.Walk u v)
    (a b : G.edgeSet) (ha : u ∈ a.val) (hb : v ∈ b.val) :
    ∃ path : (lineGraph G).Walk a b, path.length ≤ w.length+1 := by
  induction w generalizing a with
  | nil =>
    by_cases hab : a = b
    · subst b
      exact ⟨.nil,by simp⟩
    · refine ⟨(.cons ⟨hab,_,ha,hb⟩ .nil : (lineGraph G).Walk a b),?_⟩
      change 1 ≤ 1
      omega
  | @cons u z v h w ih =>
    let f : G.edgeSet := ⟨s(u,z),G.mem_edgeSet.mpr h⟩
    obtain ⟨path,hpath⟩ := ih f (by simp [f]) hb
    by_cases haf : a = f
    · subst a
      exact ⟨path,by simp only [SimpleGraph.Walk.length_cons]; omega⟩
    · refine ⟨.cons ⟨haf,u,ha,by simp [f]⟩ path,?_⟩
      change path.length+1 ≤ w.length+1+1
      omega

lemma copy_separation (ids : Fin N → ℕ) (hi : Function.Injective ids)
    (ell K : ℕ) (chi : Sym2 (Fin N) → ℕ)
    (hchi : Proper (graphPower (lineGraph G) (256*ell+1)) K (fun e => chi e.val))
    (p : Pairing N) (pick : Copy p → Fin N) (hpick : CopyEdgeChoice G p pick) :
    ReusableColors G ell (2*K) (copyColor ids chi pick) := by
  constructor
  · intro a
    have he : s(a.1,pick a) ∈ G.edgeSet := G.mem_edgeSet.mpr (hpick.1 a)
    have hc := hchi.1 ⟨s(a.1,pick a),he⟩
    change chi s(a.1,pick a) < K at hc
    unfold copyColor
    split_ifs <;> omega
  · intro a b hab hclose hcolor
    let ea : G.edgeSet := ⟨s(a.1,pick a),G.mem_edgeSet.mpr (hpick.1 a)⟩
    let eb : G.edgeSet := ⟨s(b.1,pick b),G.mem_edgeSet.mpr (hpick.1 b)⟩
    by_cases heq : ea = eb
    · have hu : a.1 ≠ b.1 := by
        intro huv
        have hh : s(a.1,pick a) = s(a.1,pick b) := by
          have he := congrArg Subtype.val heq
          change s(a.1,pick a) = s(b.1,pick b) at he
          simpa only [huv] using he
        exact hpick.2 a b huv hab (Sym2.congr_right.mp hh)
      have hswap : pick a = b.1 ∧ pick b = a.1 := by
        have he := congrArg Subtype.val heq
        change s(a.1,pick a) = s(b.1,pick b) at he
        rcases Sym2.eq_iff.mp he with h | h
        · exact False.elim (hu h.1)
        · exact ⟨h.2,h.1.symm⟩
      have hc : chi s(a.1,pick a) = chi s(b.1,pick b) := congrArg (fun e : G.edgeSet => chi e.val) heq
      have hid : ids a.1 ≠ ids b.1 := fun h => hu (hi h)
      unfold copyColor at hcolor
      rw [← hc,hswap.1,hswap.2] at hcolor
      split_ifs at hcolor <;> omega
    · obtain ⟨w,hw⟩ := hclose
      obtain ⟨path,hpath⟩ := line_walk_of_walk G w ea eb (by simp [ea]) (by simp [eb])
      have hc := hchi.2 ea eb ⟨heq,path,by omega⟩
      change chi s(a.1,pick a) ≠ chi s(b.1,pick b) at hc
      unfold copyColor at hcolor
      split_ifs at hcolor <;> omega

lemma endpoint_walk (e : G.edgeSet) (u v : Fin N) (hu : u ∈ e.val) (hv : v ∈ e.val) :
    ∃ path : G.Walk u v, path.length ≤ 1 := by
  by_cases h : u = v
  · subst v
    exact ⟨.nil,by simp⟩
  · have he : e.val = s(u,v) := (Sym2.mem_and_mem_iff h).mp ⟨hu,hv⟩
    have hadj : G.Adj u v := G.mem_edgeSet.mp (by simpa only [he] using e.property)
    exact ⟨.cons hadj .nil,by simp⟩


lemma physical_walk_of_line {a b : G.edgeSet} (w : (lineGraph G).Walk a b)
    (u v : Fin N) (hu : u ∈ a.val) (hv : v ∈ b.val) :
    ∃ path : G.Walk u v, path.length ≤ w.length+1 := by
  induction w generalizing u with
  | nil => exact endpoint_walk G _ u v hu hv
  | @cons a b c h w ih =>
    obtain ⟨z,hza,hzb⟩ := h.2
    obtain ⟨p,hp⟩ := endpoint_walk G a u z hu hza
    obtain ⟨q,hq⟩ := ih z hzb hv
    exact ⟨p.append q,by rw [SimpleGraph.Walk.length_append,SimpleGraph.Walk.length_cons]; omega⟩

lemma routed_power (r : ℕ) :
    ∃ D : Routed G G.edgeSet,
      D.graph = graphPower (lineGraph G) r ∧
      (∀ e : G.edgeSet, D.owner e ∈ e.val) ∧ RouteLength D (r+2) := by
  let owner : G.edgeSet → Fin N := fun e => e.val.out.1
  have hown (e : G.edgeSet) : owner e ∈ e.val := Sym2.out_fst_mem _
  have routes (a b : G.edgeSet) (hab : (graphPower (lineGraph G) r).Adj a b) :
      ∃ path : G.Walk (owner a) (owner b), path.length ≤ r+2 := by
    obtain ⟨w,hw⟩ := hab.2
    obtain ⟨path,hpath⟩ := physical_walk_of_line G w _ _ (hown a) (hown b)
    exact ⟨path,by omega⟩
  let D : Routed G G.edgeSet := {
    graph := graphPower (lineGraph G) r
    owner := owner
    identity := fun e => (Fintype.equivFin G.edgeSet e).val
    identity_injective := fun a b h => (Fintype.equivFin G.edgeSet).injective (Fin.ext h)
    route := fun a b h => (routes a b h).choose }
  refine ⟨D,rfl,hown,?_⟩
  intro a b h
  exact (routes a b h).choose_spec

end CopyColorProof

theorem solution (N : ℕ) (G : SimpleGraph (Fin N)) (ids : Fin N → ℕ)
    (hi : Function.Injective ids) (ell K : ℕ) (chi : Sym2 (Fin N) → ℕ)
    (hchi : Proper (graphPower (lineGraph G) (256*ell+1)) K (fun e => chi e.val)) :
    (∃ D : Routed G G.edgeSet,
      D.graph = graphPower (lineGraph G) (256*ell+1) ∧
      (∀ e : G.edgeSet, D.owner e ∈ e.val) ∧ RouteLength D (256*ell+3)) ∧
    ∀ (p : Pairing N) (pick : Copy p → Fin N), CopyEdgeChoice G p pick →
      ReusableColors G ell (2*K) (copyColor ids chi pick) := by
  exact ⟨CopyColorProof.routed_power G (256*ell+1),
    fun p pick hpick => CopyColorProof.copy_separation G ids hi ell K chi hchi p pick hpick⟩

